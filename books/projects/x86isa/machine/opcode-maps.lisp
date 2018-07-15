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
  :parents (x86isa decoding-and-spec-utils)
  :short "<b>ACL2 representation of x86 Opcode Maps</b>"
  :long "<p>The constants @('*one-byte-opcode-map-lst*'),
 @('*two-byte-opcode-map-lst*'), @('*0F-38-three-byte-opcode-map-lst*'),
 @('*0F-3A-three-byte-opcode-map-lst*'), and
 @('*opcode-extensions-by-group-number*') contain information presented in the
 opcode maps, as described in Intel Manual, Volume 2, Appendix A.</p>")

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

(defconst *one-byte-opcode-map-lst*
  ;; Source: Intel Volume 2, Table A-2.

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

    #| 40 |# (((:o64  . (:rex))       (:i64 . ("INC"  1 (:eAX))))
              ((:o64  . (:rex-b))     (:i64 . ("INC"  1 (:eCX))))
              ((:o64  . (:rex-x))     (:i64 . ("INC"  1 (:eDX))))
              ((:o64  . (:rex-xb))    (:i64 . ("INC"  1 (:eBX))))
              ((:o64  . (:rex-r))     (:i64 . ("INC"  1 (:eSP))))
              ((:o64  . (:rex-rb))    (:i64 . ("INC"  1 (:eBP))))
              ((:o64  . (:rex-rx))    (:i64 . ("INC"  1 (:eSI))))
              ((:o64  . (:rex-rxb))   (:i64 . ("INC"  1 (:eDI))))
              ((:o64  . (:rex-w))     (:i64 . ("DEC"  1 (:eAX))))
              ((:o64  . (:rex-wb))    (:i64 . ("DEC"  1 (:eCX))))
              ((:o64  . (:rex-wx))    (:i64 . ("DEC"  1 (:eDX))))
              ((:o64  . (:rex-wxb))   (:i64 . ("DEC"  1 (:eBX))))
              ((:o64  . (:rex-wr))    (:i64 . ("DEC"  1 (:eSP))))
              ((:o64  . (:rex-wrb))   (:i64 . ("DEC"  1 (:eBP))))
              ((:o64  . (:rex-wrx))   (:i64 . ("DEC"  1 (:eSI))))
              ((:o64  . (:rex-wrxb))  (:i64 . ("DEC"  1 (:eDI)))))

    #| 50 |# (("PUSH" 1 (:rAX/r8)   :d64)
              ("PUSH" 1 (:rCX/r9)   :d64)
              ("PUSH" 1 (:rDX/r10)  :d64)
              ("PUSH" 1 (:rBX/r11)  :d64)
              ("PUSH" 1 (:rSP/r11)  :d64)
              ("PUSH" 1 (:rBP/r13)  :d64)
              ("PUSH" 1 (:rSI/r14)  :d64)
              ("PUSH" 1 (:rDI/r15)  :d64)
              ("POP"  1 (:rAX/r8)   :d64)
              ("POP"  1 (:rCX/r9)   :d64)
              ("POP"  1 (:rDX/r10)  :d64)
              ("POP"  1 (:rBX/r11)  :d64)
              ("POP"  1 (:rSP/r11)  :d64)
              ("POP"  1 (:rBP/r13)  :d64)
              ("POP"  1 (:rSI/r14)  :d64)
              ("POP"  1 (:rDI/r15)  :d64))

    #| 60 |# (((:i64 . ("PUSHA/PUSHAD" 0)))
              ((:i64 . ("POPA/POPAD"   0)))
              ((:i64 . ("BOUND"  2 (G v) (M a))))
              ((:o64 . ("MOVSXD" 2 (G v) (E v)))
               (:i64 . ("ARPL"   2 (E w) (G w))))
              (:prefix-FS)
              (:prefix-GS)
              (:prefix-OpSize)
              (:prefix-AddrSize)
              ("PUSH" 1 (I z) :d64)
              ("IMUL"  3 (G v) (E v) (I z))
              ("PUSH" 1 (I b) :d64)
              ("IMUL"  3 (G v) (E v) (I b))
              ("INS/INSB" 2 (Y b) (D x))
              ("INS/INSW/INSD" 2 (Y z) (D x))
              ("OUTS/OUTSB" 2 (Y b) (D x))
              ("OUTS/OUTSW/OUTSD" 2 (Y z) (D x)))

    #| 70 |# (("JO" 1 (J b) :f64)
              ("JNO" 1 (J b) :f64)
              ("JB/NAE/C" 1 (J b) :f64)
              ("JNB/AE/NC" 1 (J b) :f64)
              ("JZ/E" 1 (J b) :f64)
              ("JNZ/NE" 1 (J b) :f64)
              ("JBE/NA" 1 (J b) :f64)
              ("JNBE/A" 1 (J b) :f64)
              ("JS" 1 (J b) :f64)
              ("JNS" 1 (J b) :f64)
              ("JP/PE" 1 (J b) :f64)
              ("JNP/PO" 1 (J b) :f64)
              ("JL/NGE" 1 (J b) :f64)
              ("JNL/GE" 1 (J b) :f64)
              ("JLE/NG" 1 (J b) :f64)
              ("JNLE/G" 1 (J b) :f64))

    #| 80 |#  ((:Group-1 2 (E b) (I b) :1a)
               (:Group-1 2 (E v) (I z) :1a)
               ((:i64 . (:Group-1 2 (E b) (I b) :1a)))
               (:Group-1 2 (E v) (I b) :1a)
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
               ;; in Table A-6, Grp 1A only contains POP,
               ;; so we leave the latter implicit here:
               (:Group-1A 1 (E v) :1a :d64))

    #| 90 |# (("XCHG" 1 (:r8))
              ("XCHG" 2 (:rCX/r9)  (:rAX))
              ("XCHG" 2 (:rDX/r10) (:rAX))
              ("XCHG" 2 (:rBX/r11) (:rAX))
              ("XCHG" 2 (:rSP/r12) (:rAX))
              ("XCHG" 2 (:rBP/r13) (:rAX))
              ("XCHG" 2 (:rSI/r14) (:rAX))
              ("XCHG" 2 (:rDI/r15) (:rAX))
              ("CBW/CWDE/CDQE" 0)
              ("CWD/CDQ/CQO" 0)
              ((:i64 . ("CALL" 1 (A p))))
              ("FWAIT/WAIT" 0)
              ("PUSHF/D/Q"  1 (F v) :d64)
              ("POPF/D/Q"   1 (F v) :d64)
              ("SAHF" 0)
              ("LAHF" 0))

    #| a0 |# (("MOV" 2 (:AL) (O b))
              ("MOV" 2 (:rAX) (O v))
              ("MOV" 2 (O b) (:AL))
              ("MOV" 2 (O v) (:rAX))
              ("MOVS/B" 2 (Y b) (X b))
              ("MOVS/W/D/Q" 2 (Y v) (X v))
              ("CMPS/B"   2 (X b) (Y b))
              ("CMPS/W/D" 2 (X v) (Y v))
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
              ("MOV" 2  (:rAX/r8)  (I v))
              ("MOV" 2  (:rCX/r9)  (I v))
              ("MOV" 2  (:rDX/r10) (I v))
              ("MOV" 2  (:rBX/r11) (I v))
              ("MOV" 2  (:rSP/r12) (I v))
              ("MOV" 2  (:rBP/r13) (I v))
              ("MOV" 2  (:rSI/r14) (I v))
              ("MOV" 2  (:rDI/r15) (I v)))

    #| c0 |# ((:Group-2 2 (E b) (I b) :1a)
              (:Group-2 2 (E v) (I b) :1a)
              ("RET" 1 (I w) :f64)
              ("RET" 0 :f64)
              ;; C4 and C5 are first bytes of the vex prefixes, both
              ;; in 32-bit and IA-32e modes.  However, in the 32-bit
              ;; and compatibility modes, the second byte determines
              ;; whether the instruction is LES/LDS or a VEX
              ;; instruction.  We use :o64 here because we're sure
              ;; that an "opcode" of C4 and C5 in the 64-bit mode will
              ;; not have a modr/m corresponding to it --- basically,
              ;; we shouldn't be looking up modr/m info. for these
              ;; opcodes in the 64-bit mode.
              ((:o64 . (:vex3-byte0))  (:i64 . ("LES" 2 (G z) (M p))))
              ((:o64 . (:vex2-byte0))  (:i64 . ("LDS" 2 (G z) (M p))))
              (:Group-11 2 (E b) (I b) :1a)
              (:Group-11 2 (E v) (I z) :1a)
              ("ENTER" 2 (I w) (I b))
              ("LEAVE" 0 :d64)
              ("RET" 1 (I w))
              ("RET" 0)
              ("INT 3" 0)
              ("INT" 1 (I b))
              ((:i64 . ("INTO" 0)))
              ("IRET/D/Q" 0))

    #| d0 |# ((:Group-2 2 (E b) (1) :1a)
              (:Group-2 2 (E v) (1) :1a)
              (:Group-2 2 (E b) (:CL) :1a)
              (:Group-2 2 (E v) (:CL) :1a)
              ((:i64 . ("AAM" 1 (I b))))
              ((:i64 . ("AAD" 1 (I b))))
              (:none)
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

    #| e0 |# (("LOOPNE/LOOPNZ" 1 (J b) :f64)
              ("LOOPE/LOOPZ" 1 (J b) :f64)
              ("LOOP" 1 (J b) :f64)
              ("JrCXZ" 1 (J b) :f64)
              ("IN" 2 (:AL) (I b))
              ("IN" 2 (:eAX) (I b))
              ("OUT" 2 (I b) (:AL))
              ("OUT" 2 (I b) (:eAX))
              ("CALL" 1 (J z) :f64)
              ("JMP"  1 (J z) :f64)
              ((:i64 . ("JMP"  1 (A p))))
              ("JMP"  1 (J b) :f64)
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
              (:Group-3 1 (E b) :1a)
              (:Group-3 1 (E v) :1a)
              ("CLC" 0)
              ("STC" 0)
              ("CLI" 0)
              ("STI" 0)
              ("CLD" 0)
              ("STD" 0)
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
              (:none)
              ((:o64 . ("SYSCALL" 0)))
              ("CLTS" 0)
              ((:o64 . ("SYSRET" 0)))
    #| 08 |#  ("INVD" 0)
              ("WBINVD" 0)
              (:none)
              ("UD2" 0 :1b)
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

              ((:no-prefix . ("VMOVHPS"    3 (V dq)  (H q)  (M q) :v1))
               (:no-prefix . ("VMOVLHPS"   3 (V dq)  (H q)  (U q)))
               (:66        . ("VMOVHPD"    3 (V dq)  (H q)  (M q) :v1))
               (:F3        . ("VMOVSHDUP"  2 (V x)   (W x))))

              ((:no-prefix . ("VMOVHPS"    2 (M q)  (V q) :v1))
               (:66        . ("VMOVHPD"    2 (M q)  (V q) :v1)))

    #| 18 |#  (:Group-16 0 :1a)

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

              (:Group-12 0 :1a)

              (:Group-13 0 :1a)

              (:Group-14 0 :1a)

              ((:no-prefix . ("PCMPEQB"     2 (P q)   (Q q)))
               (:66        . ("VPCMPEQB"    3 (V x)   (H x)  (W x))))

              ((:no-prefix . ("PCMPEQW"     2 (P q)   (Q q)))
               (:66        . ("VPCMPEQW"    3 (V x)   (H x)  (W x))))

              ((:no-prefix . ("PCMPEQD"     2 (P q)   (Q q)))
               (:66        . ("VPCMPEQD"    3 (V x)   (H x)  (W x))))

              ((:no-prefix . ("EMMS"        0))
               (:no-prefix . ("VZEROUPPER"  0 :v))
               (:no-prefix . ("VZEROALL"    0 :v)))

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

    #| 80 |#  (("JO" 1 (J z) :f64)
               ("JNO" 1 (J z) :f64)
               ("JB/NAE/C" 1 (J z) :f64)
               ("JNB/AE/NC" 1 (J z) :f64)
               ("JZ/E" 1 (J z) :f64)
               ("JNZ/NE" 1 (J z) :f64)
               ("JBE/NA" 1 (J z) :f64)
               ("JNBE/A" 1 (J z) :f64)
    #| 88 |#   ("JS" 1 (J z) :f64)
               ("JNS" 1 (J z) :f64)
               ("JP/PE" 1 (J z) :f64)
               ("JNP/PO" 1 (J z) :f64)
               ("JL/NGE" 1 (J z) :f64)
               ("JNL/GE" 1 (J z) :f64)
               ("JLE/NG" 1 (J z) :f64)
               ("JNLE/G" 1 (J z) :f64))

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

    #| a0 |# (("PUSH"  1 (:FS) :d64)
              ("POP"   1 (:FS) :d64)
              ("CPUID" 0)
              ("BT" 2 (E v) (G v))
              ("SHLD" 3 (E v) (G v) (I b))
              ("SHLD" 3 (E v) (G v) (:CL))
              (:none)
              (:none)
    #| a8 |#  ("PUSH"  1 (:GS) :d64)
              ("POP"   1 (:GS) :d64)
              ("RSM" 0)
              ("BTS" 2 (E v) (G v))
              ("SHRD" 3 (E v) (G v) (I b))
              ("SHRD" 3 (E v) (G v) (:CL))
              (:Group-15 0 :1a :1c)
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

              ((:no-prefix . (:Group-10 0 :1a))
               (:no-prefix . ("InvalidOpcode" 0 :1b)))

              (:Group-8 2 (E v) (I b) :1a)

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
              ((:no-prefix . (:none))
               (:66        . ("VPERMILPSV"      3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPERMILPDV"      3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VTESTPSV"        2 (V x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VTESTPDV"        2 (V x) (W x) :v))))

    #| 10 |# (((:66        . ("PBLENDVB"        2 (V dq) (W dq))))
              (:none)
              (:none)
              ((:66        . ("VCVTPH2PSV"      3 (V x)  (W x)  (I b) :v)))
              ((:66        . ("BLENDVPS"        2 (V dq) (W dq))))
              ((:66        . ("BLENDVPD"        2 (V dq) (W dq))))
              ((:66        . ("VPERMPSV"        3 (V qq) (H qq) (W qq) :v)))
              ((:66        . ("VPTEST"          2 (V x)  (W x))))
    #| 18 |#  ((:no-prefix . (:none))
               (:66        . ("VBROADCASTSSV"   2 (V x)  (W d) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VBROADCASTSDV"   2 (V qq) (W q) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VBROADCASTF128V" 2 (V qq) (M dq) :v)))
              (:none)
              ((:no-prefix . ("PABSB"           2 (P q)  (Q q)))
               (:66        . ("VPABSB"          2 (V x)  (W x))))
              ((:no-prefix . ("PABSW"           2 (P q)  (Q q)))
               (:66        . ("VPABSW"          2 (V x)  (W x))))
              ((:no-prefix . ("PABSD"           2 (P q)  (Q q)))
               (:66        . ("VPABSD"          2 (V x)  (W x))))
              (:none))

    #| 20 |# (((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVSXBW" 2 (V x) (U x))
                                    ("VPMOVSXBW" 2 (V x) (M q))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVSXBD" 2 (V x) (U x))
                                    ("VPMOVSXBD" 2 (V x) (M d))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVSXBQ" 2 (V x) (U x))
                                    ("VPMOVSXBQ" 2 (V x) (M w))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVSXWD" 2 (V x) (U x))
                                    ("VPMOVSXWD" 2 (V x) (M q))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVSXWQ" 2 (V x) (U x))
                                    ("VPMOVSXWQ" 2 (V x) (M d))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVSXDQ" 2 (V x) (U x))
                                    ("VPMOVSXDQ" 2 (V x) (M q))))))
              (:none)
              (:none)
    #| 28 |#  ((:no-prefix . (:none))
               (:66        . ("VPMULDQ"     3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPCMPEQQ"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VMOVNTDQA"   2 (V x) (M x))))
              ((:no-prefix . (:none))
               (:66        . ("VPACKUSDW"   3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VMASKMOVPS"  3 (V x) (H x) (M x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VMASKMOVPD"  3 (V x) (H x) (M x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VMASKMOVPS"  3 (M x) (H x) (V x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VMASKMOVPD"  3 (M x) (H x) (V x) :v))))

    #| 30 |# (((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVZXBW" 2 (V x)  (U x))
                                    ("VPMOVZXBW" 2 (V x)  (M q))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVZXBD" 2 (V x)  (U x))
                                    ("VPMOVZXBD" 2 (V x)  (M d))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVZXBQ" 2 (V x)  (U x))
                                    ("VPMOVZXBQ" 2 (V x)  (M w))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVZXWD" 2 (V x)  (U x))
                                    ("VPMOVZXWD" 2 (V x)  (M q))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVZXWQ" 2 (V x)  (U x))
                                    ("VPMOVZXWQ" 2 (V x)  (M d))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPMOVZXDQ" 2 (V x)  (U x))
                                    ("VPMOVZXDQ" 2 (V x)  (M q))))))
              ((:no-prefix . (:none))
               (:66        . ("VPERMD"     3 (V qq) (H qq) (W qq) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPCMPGTQ"   3 (V x) (Hx) (W x))))
    #| 38 |#  ((:no-prefix . (:none))
               (:66        . ("VPMINSB"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMINSD"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMINUW"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMINUD"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMAXSB"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMAXSD"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMAXUW"    3 (V x) (H x) (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPMAXUD"    3 (V x) (H x) (W x)))))

    #| 40 |# (((:no-prefix . (:none))
               (:66        . ("VPMULLD"     3 (V x)  (H x)    (W x))))
              ((:no-prefix . (:none))
               (:66        . ("VPHMINPOSUW" 2 (V dq) (W dq))))
              (:none)
              (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VPSRLVD/Q"   3  (V x) (H x)    (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPSRAVD"     3  (V x) (H x)    (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPSLLVD/Q"   3  (V x) (H x)    (W x) :v)))
    #| 48 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 50 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 58 |#  ((:no-prefix . (:none))
               (:66        . ("VPBROADCASTD"   2  (V x)  (W x)  :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPBROADCASTQ"   2  (V x)  (W x)  :v)))
              ((:no-prefix . (:none))
               (:66        . ("VBROADCASTI128" 2  (V qq) (M dq) :v)))
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 60 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 68 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 70 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 78 |#  ((:no-prefix . (:none))
               (:66        . ("VPBROADCASTB" 2 (V x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPBROADCASTW" 2 (V x) (W x) :v)))
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 80 |#  (((:no-prefix . (:none))
                (:66        . ("INVEPT"  2 (G y) (M dq))))
               ((:no-prefix . (:none))
                (:66        . ("INVVPID" 2 (G y) (M dq))))
               ((:no-prefix . (:none))
                (:66        . ("INVPCID" 2 (G y) (M dq))))
               (:none)
               (:none)
               (:none)
               (:none)
               (:none)
    #| 88 |#   (:none)
               (:none)
               (:none)
               (:none)
               ((:no-prefix . (:none))
                (:66        . ("VPMASKMOVD/Q" 3 (V x) (H x) (M x) :v)))
               (:none)
               ((:no-prefix . (:none))
                (:66        . ("VPMASKMOVD/Q" 3 (M x) (V x) (H x) :v)))
               (:none))

    #| 90 |# (((:no-prefix . (:none))
               (:66        . ("VGATHERDD/Q"      3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VGATHERQD/Q"      3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VGATHERDPS/D"     3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VGATHERQPS/D"     3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . (:none)))
              ((:no-prefix . (:none))
               (:66        . (:none)))
              ((:no-prefix . (:none))
               (:66        . ("VFMADDSUB132PS/D" 3 (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUBADD132PS/D" 3 (V x) (H x) (W x) :v)))
    #| 98 |#  ((:no-prefix . (:none))
               (:66        . ("VFMADD132PS/D"    3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMADD132SS/D"    3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUB132PS/D"    3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUB132SS/D"    3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMADD132PS/D"   3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMADD132SS/D"   3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMSUB132PS/D"   3  (V x) (H x) (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMSUB132SS/D"   3  (V x) (H x) (W x) :v))))

    #| a0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VFMADDSUB213PS/D" 3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUBADD213PS/D" 3 (V x)  (H x)  (W x) :v)))
    #| a8 |#  ((:no-prefix . (:none))
               (:66        . ("VFMADD213PS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMADD213SS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUB213PS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUB213SS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMADD213PS/D"   3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMADD213SS/D"   3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMSUB213PS/D"   3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMSUB213SS/D"   3 (V x)  (H x)  (W x) :v))))

    #| b0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VFMADDSUB231PS/D" 3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUBADD231PS/D" 3 (V x)  (H x)  (W x) :v)))
    #| b8 |#  ((:no-prefix . (:none))
               (:66        . ("VFMADD231PS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMADD231SS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUB231PS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFMSUB231SS/D"    3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMADD231PS/D"   3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMADD231SS/D"   3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMSUB231PS/D"   3 (V x)  (H x)  (W x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VFNMSUB231SS/D"   3 (V x)  (H x)  (W x) :v))))

    #| c0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| c8 |#  ("SHA1NEXTE"   2 (V dq) (W dq))
              ("SHA1MSG1"    2 (V dq) (W dq))
              ("SHA1MSG2"    2 (V dq) (W dq))
              ("SHA256RNDS2" 2 (V dq) (W dq))
              ("SHA256MSG1"  2 (V dq) (W dq))
              ("SHA256MSG2"  2 (V dq) (W dq))
              (:none)
              (:none))

  #| d0 |# ((:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
  #| d8 |#  (:none)
            (:none)
            (:none)
            ((:no-prefix . (:none))
             (:66        . ("VAESIMC"     2 (V dq) (W dq))))
            ((:no-prefix . (:none))
             (:66        . ("VAESENC"     3 (V dq) (H dq) (W dq))))
            ((:no-prefix . (:none))
             (:66        . ("VAESENCLAST" 3 (V dq) (H dq) (W dq))))
            ((:no-prefix . (:none))
             (:66        . ("VAESDEC"     3 (V dq) (H dq) (W dq))))
            ((:no-prefix . (:none))
             (:66        . ("VAESDECLAST" 3 (V dq) (H dq) (W dq)))))

  #| e0 |# ((:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
  #| e8 |#  (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none))

  #| f0 |# (((:no-prefix    . ("MOVBE" 2 (G y)  (M y)))
             (:66           . ("MOVBE" 2 (G w)  (M w)))
             (:F3           . (:none))
             (:F2           . ("CRC32" 2 (G d)  (E b)))
             ((:66 :F2)     . ("CRC32" 2 (G d)  (E b))))
            ((:no-prefix    . ("MOVBE" 2 (M y)  (G y)))
             (:66           . ("MOVBE" 2 (M w)  (G w)))
             (:F3           . (:none))
             (:F2           . ("CRC32" 2 (G d)  (E y)))
             ((:66 :F2)     . ("CRC32" 2 (G d)  (E w))))
            ((:no-prefix    . ("ANDN"  3 (G y)  (B y)  (E y) :v))
             (:66           . (:none))
             (:F3           . (:none))
             (:F2           . (:none))
             ((:66 :F2)     . (:none)))
            (:Group-17 0 :1a)
            ((:no-prefix    . (:none))
             (:66           . (:none))
             (:F3           . (:none))
             (:F2           . (:none))
             ((:66 :F2)     . (:none)))
            ((:no-prefix    . ("BZHI"  3 (G y)  (E y)  (B y) :v))
             (:66           . (:none))
             (:F3           . ("PEXT"  3 (G y)  (B y)  (E y) :v))
             (:F2           . ("PDEP"  3 (G y)  (B y)  (E y) :v))
             ((:66 :F2)     . (:none)))
            ((:no-prefix    . (:none))
             (:66           . ("ADCX"  2 (G y)  (E y)))
             (:F3           . ("ADOX"  2 (G y)  (E y)))
             (:F2           . ("MULX"  3 (B y)  (G y)  (:rDX)  (E y) :v))
             ((:66 :F2)     . (:none)))
            ((:no-prefix    . ("BEXTR" 3 (G y)  (E y)  (B y) :v))
             (:66           . ("SHLX"  3 (G y)  (E y)  (B y) :v))
             (:F3           . ("SARX"  3 (G y)  (E y)  (B y) :v))
             (:F2           . ("SHRX"  3 (G y)  (E y)  (B y) :v))
             ((:66 :F2)     . (:none)))
  #| f8 |#  (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none)
            (:none))

  #|       -------------------------------        |#
  ))

(defconst *0F-3A-three-byte-opcode-map-lst*
  ;; First two bytes are 0x0F 0x3A.
  ;; Source: Intel Volume 2, Table A-5.

  '(
    #|       -------------------------------        |#


    #| 00 |# (((:no-prefix . (:none))
               (:66        . ("VPERMQ"     3 (V qq)  (W qq)  (I b) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPERMPD"    3 (V qq)  (W qq)  (I b) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPBLENDD"   4 (V x)   (H x)   (W x)  (I b) :v)))
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VPERMILPS"  3 (V x)  (W x)  (I b) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPERMILPD"  3 (V x)  (W x)  (I b) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPERM2F128" 4 (V qq) (H qq) (W qq) (I b) :v)))
              (:none)
    #| 08 |#  ((:no-prefix . (:none))
               (:66        . ("VROUNDPS" 3 (V x)  (W x)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VROUNDPD" 3 (V x)  (W x)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VROUNDSS" 3 (V ss) (W ss) (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VROUNDSD" 3 (V sd) (W sd) (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VBLENDPS" 4 (V x)  (H x)  (W x) (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VBLENDPD" 4 (V x)  (H x)  (W x) (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VPBLENDW" 4 (V x)  (H x)  (W x) (I b))))
              ((:no-prefix . ("PALIGNR"  3 (P q)  (Q q)  (I b)))
               (:66        . ("VPALIGNR" 4 (V x)  (H x)  (W x) (I b)))))

    #| 10 |# ((:none)
              (:none)
              (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPEXTRB"    3 (R d)  (V dq)  (I b))
                                    ("VPEXTRB"    3 (M b)  (V dq)  (I b))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPEXTRW"    3 (R d)  (V dq)  (I b))
                                    ("VPEXTRW"    3 (M w)  (V dq)  (I b))))))
              ((:no-prefix . (:none))
               (:66        . ("VPEXTRD/Q"   3 (E y)  (V dq)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VEXTRACTPS"  3 (E d)  (V dq)  (I b))))
    #| 18 |#  ((:no-prefix . (:none))
               (:66        . ("VINSERTF128"  4 (V qq) (H qq) (W qq) (I b) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VEXTRACTF128" 3 (W dq) (V qq) (I b) :v)))
              (:none)
              (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VCVTPS2PH"    3 (W x)  (V x)  (I b) :v)))
              (:none)
              (:none))

    #| 20 |# (((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VPINSRB"   4 (V dq) (H dq) (R y)  (I b))
                                    ("VPINSRB"   4 (V dq) (H dq) (M b) (I b))))))
              ((:no-prefix . (:none))
               (:66        . (:ALT .
                                   (("VINSERTPS" 4 (V dq) (H dq) (U dq) (I b))
                                    ("VINSERTPS" 4 (V dq) (H dq) (M d) (I b))))))
              ((:no-prefix . (:none))
               (:66        . ("VPINSRD/Q"  4 (V dq) (H dq) (E y)  (I b))))
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 28 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 30 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 38 |#  ((:no-prefix . (:none))
               (:66        . ("VINSERTI128"  4 (V qq) (H qq) (W qq) (I b) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VEXTRACTI128" 3 (W dq) (V qq) (I b) :v)))
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 40 |# (((:no-prefix . (:none))
               (:66        . ("VDPPS"      4 (V x)  (H x)  (W x)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VDPPD"      4 (V dq) (H dq) (W dq) (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VMPSADBW"   4 (V x)  (H x)  (W x)  (I b))))
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VPCLMULQDQ" 4 (V dq) (H dq) (W dq) (I b))))
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VPERM2I128" 4 (V qq) (H qq) (W qq) (I b) :v)))
              (:none)
    #| 48 |#  (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VBLENDVPS"  4 (V x)  (H x)  (W x)  (L x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VBLENDVPD"  4 (V x)  (H x)  (W x)  (L x) :v)))
              ((:no-prefix . (:none))
               (:66        . ("VPBLENDVB"  4 (V x)  (H x)  (W x)  (L x) :v)))
              (:none)
              (:none)
              (:none))

    #| 50 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 58 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 60 |# (((:no-prefix . (:none))
               (:66        . ("VPCMPESTRM" 3 (V dq)  (W dq)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VPCMPESTRI" 3 (V dq)  (W dq)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VPCMPISTRM" 3 (V dq)  (W dq)  (I b))))
              ((:no-prefix . (:none))
               (:66        . ("VPCMPISTRI" 3 (V dq)  (W dq)  (I b))))
              (:none)
              (:none)
              (:none)
              (:none)
    #| 68 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 70 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 78 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 80 |#  ((:none)
               (:none)
               (:none)
               (:none)
               (:none)
               (:none)
               (:none)
               (:none)
    #| 88 |#   (:none)
               (:none)
               (:none)
               (:none)
               (:none)
               (:none)
               (:none)
               (:none))

    #| 90 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| 98 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| a0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| a8 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| b0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| b8 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| c0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| c8 |#  (:none)
              (:none)
              (:none)
              (:none)
              ("SHA1RNDS4" 3 (V dq) (W dq) (I b))
              (:none)
              (:none)
              (:none))

    #| d0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| d8 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              ((:no-prefix . (:none))
               (:66        . ("VAESKEYGEN" 3 (V dq)  (W dq)  (I b)))))

    #| e0 |# ((:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| e8 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| f0 |# (((:no-prefix . (:none))
               (:F2        . ("RORX" 3 (G y)  (E y)  (I b) :v)))
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
    #| f8 |#  (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

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
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("ADD" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ("OR" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("ADC" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("SBB" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("AND" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("SUB" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("XOR" 2 (E b) (I b) :1a))
               (((:opcode . #x80)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ("CMP" 2 (E b) (I b) :1a))

               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("ADD" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ("OR" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("ADC" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("SBB" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("AND" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("SUB" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("XOR" 2 (E v) (I z) :1a))
               (((:opcode . #x81)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ("CMP" 2 (E v) (I z) :1a))

               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ((:i64 . ("ADD" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ((:i64 . ("OR" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ((:i64 . ("ADC" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ((:i64 . ("SBB" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ((:i64 . ("AND" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ((:i64 . ("SUB" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ((:i64 . ("XOR" 2 (E b) (I b) :1a))))
               (((:opcode . #x82)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ((:i64 . ("CMP" 2 (E b) (I b) :1a))))

               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("ADD" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ("OR" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("ADC" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("SBB" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("AND" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("SUB" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("XOR" 2 (E v) (I b) :1a))
               (((:opcode . #x83)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ("CMP" 2 (E v) (I b) :1a))))

    (:Group-1A . ;; Covers opcode 8F.
               ((((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("POP" 1 (E v) :1a :d64))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #x8F)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (:none))))

    (:Group-2  . ;; Covers opcodes
               ;; (C0, C1 reg, imm),
               ;; (D0, D1 reg, 1),
               ;; and
               ;; (D2, D3 reg, CL).
               ((((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("ROL" 2 (E b) (I b) :1a))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("ROR" 2 (E b) (I b) :1a))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("RCL" 2 (E b) (I b) :1a))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("RCR" 2 (E b) (I b) :1a))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("SHL/SAL" 2 (E b) (I b) :1a))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("SHR" 2 (E b) (I b) :1a))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("SAR" 2 (E b) (I b) :1a))

                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("ROL" 2 (E v) (I b) :1a))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("ROR" 2 (E v) (I b) :1a))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("RCL" 2 (E v) (I b) :1a))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("RCR" 2 (E v) (I b) :1a))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("SHL/SAL" 2 (E v) (I b) :1a))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("SHR" 2 (E v) (I b) :1a))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("SAR" 2 (E v) (I b) :1a))

                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("ROL" 2 (E b) (1) :1a))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("ROR" 2 (E b) (1) :1a))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("RCL" 2 (E b) (1) :1a))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("RCR" 2 (E b) (1) :1a))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("SHL/SAL" 2 (E b) (1) :1a))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("SHR" 2 (E b) (1) :1a))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xD0)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("SAR" 2 (E b) (1) :1a))

                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("ROL" 2 (E v) (1) :1a))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("ROR" 2 (E v) (1) :1a))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("RCL" 2 (E v) (1) :1a))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("RCR" 2 (E v) (1) :1a))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("SHL/SAL" 2 (E v) (1) :1a))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("SHR" 2 (E v) (1) :1a))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xD1)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("SAR" 2 (E v) (1) :1a))

                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("ROL" 2 (E b) (:CL) :1a))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("ROR" 2 (E b) (:CL) :1a))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("RCL" 2 (E b) (:CL) :1a))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("RCR" 2 (E b) (:CL) :1a))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("SHL/SAL" 2 (E b) (:CL) :1a))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("SHR" 2 (E b) (:CL) :1a))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xD2)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("SAR" 2 (E b) (:CL) :1a))

                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("ROL" 2 (E v) (:CL) :1a))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("ROR" 2 (E v) (:CL) :1a))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("RCL" 2 (E v) (:CL) :1a))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("RCR" 2 (E v) (:CL) :1a))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("SHL/SAL" 2 (E v) (:CL) :1a))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("SHR" 2 (E v) (:CL) :1a))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xD3)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("SAR" 2 (E v) (:CL) :1a))))

    (:Group-3 . ;; Covers opcodes F6 and F7.
              ((((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("TEST" 1 (E b) :1a))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("NOT" 1 (E b) :1a))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("NEG" 1 (E b) :1a))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("MUL" 1 (E b) :1a))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("IMUL" 1 (E b) :1a))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("DIV" 1 (E b) :1a))
               (((:opcode . #xF6)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ("IDIV" 1 (E b) :1a))))

    (:Group-4 . ;; Covers opcode FE.
              ((((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("INC" 1 (E b) :1a))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ("DEC" 1 (E b) :1a))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . #xFE)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 (:none))))

    (:Group-5 . ;; Covers opcode FF.
              ((((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("INC" 1 (E v) :1a))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ("DEC" 1 (E v) :1a))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("near CALL"  1 (E v) :1a :f64))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("far CALL"  1 (E p) :1a))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("near JMP"  1 (E v) :1a :f64))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("far JMP"  1 (M p) :1a))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("PUSH"  1 (E v) :1a :d64))
               (((:opcode . #xFF)
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 (:none))))


    (:Group-6 . ;; Covers opcode 0F 00.
              ((((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 (("SLDT" 1 (R v) :1a)
                  ("SLDT" 1 (M w) :1a)))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 (("STR" 1 (R v) :1a)
                  ("STR" 1 (M w) :1a)))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("LLDT" 1 (E w) :1a))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("LTR" 1 (E w) :1a))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("VERR" 1 (E w) :1a))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("VERW" 1 (E w) :1a))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #x00))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 (:none))))

    (:Group-7 . ;; Covers opcode 0F 01.
              ((((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :mem)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 ("SGDT" 1 (M s) :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b000)
                 (:r/m    . #b001)) .
                 ("VMCALL" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b000)
                 (:r/m    . #b010)) .
                 ("VMLAUNCH" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b000)
                 (:r/m    . #b011)) .
                 ("VMRESUME" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b000)
                 (:r/m    . #b100)) .
                 ("VMXOFF" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :mem)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 ("SIDT" 1 (M s) :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b001)
                 (:r/m    . #b000)) .
                 ("MONITOR" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b001)
                 (:r/m    . #b001)) .
                 ("MWAIT" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b001)
                 (:r/m    . #b010)) .
                 ("CLAC" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b001)
                 (:r/m    . #b011)) .
                 ("STAC" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b001)
                 (:r/m    . #b111)) .
                 ("ENCLS" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :mem)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 ("LGDT" 1 (M s) :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :mem)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 ("LIDT" 1 (M s) :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b011)
                 (:r/m    . #b000)) .
                 ("XGETBV" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b011)
                 (:r/m    . #b001)) .
                 ("XSETBV" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b011)
                 (:r/m    . #b100)) .
                 ("VMFUNC" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b011)
                 (:r/m    . #b101)) .
                 ("XEND" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b011)
                 (:r/m    . #b110)) .
                 ("XTEST" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b011)
                 (:r/m    . #b111)) .
                 ("ENCLU" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 (("SMSW" 1 (M w) :1a)
                  ("SMSW" 1 (R v) :1a)))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . #b11)) .
                 (:none))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("LMSW" 1 (E w) :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :mem)) .
                 ("INVLPG" 1 (M b) :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b111)
                 (:r/m    . #b000)) .
                 ("SWAPGS" 0 :1a))
               (((:opcode . (#x0F #x01))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b111)
                 (:r/m    . #b001)) .
                 ("RDTSCP" 0 :1a))))

    (:Group-8 . ;; Covers opcode 0F BA.
              ((((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 ("BT" 2 (E v) (I b) :1a))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 ("BTS" 2 (E b) (I b) :1a))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("BTR" 2 (E b) (I b) :1a))
               (((:opcode . (#x0F #xBA))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ("BTC" 2 (E b) (I b) :1a))))

    (:Group-9 . ;; Covers opcode 0F C7.
              ((((:opcode . (#x0F #xC7))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b000)
                 (:r/m    . :any)) .
                 (:any))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :none)
                 (:mod    . :mem)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 (("CMPXCH8B" 1 (M q) :1a)
                  ("CMPXCHG16B" 1 (M dq) :1a)))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :any)
                 (:mod    . #b11)
                 (:reg    . #b001)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b010)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b011)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b100)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :any)
                 (:mod    . :any)
                 (:reg    . #b101)
                 (:r/m    . :any)) .
                 (:none))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :none)
                 (:mod    . :mem)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("VMPTRLD" 1 (M q) :1a))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :66)
                 (:mod    . :mem)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("VMCLEAR" 1 (M q) :1a))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :F3)
                 (:mod    . :mem)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("VMXON" 1 (M q) :1a))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :none)
                 (:mod    . #b11)
                 (:reg    . #b110)
                 (:r/m    . :any)) .
                 ("RDRAND" 1 (R v) :1a))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :none)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 ("RDSEED" 1 (R v) :1a))
               (((:opcode . (#x0F #xC7))
                 (:prefix . :F3)
                 (:mod    . :any)
                 (:reg    . #b111)
                 (:r/m    . :any)) .
                 (("RDPID" 1 (R d) :1a)
                  ("RDPID" 1 (R q) :1a)))))

    (:Group-10 . ;; Covers opcode 0F B9.
               ((((:opcode . (#x0F #xB9))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . :any)
                  (:r/m    . :any)) .
                  ("UD1" 0 :1a))))

    (:Group-11 . ;; Covers opcodes C6 and C7.
               ((((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("MOV" 2 (E b) (I b) :1a))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . :mem)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC6)
                  (:prefix . :any)
                  (:mod    . #b11)
                  (:reg    . #b111)
                  (:r/m    . #b000)) .
                  ("XABORT" 1 (I b) :1a))

                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("MOV" 2 (E v) (I z) :1a))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . :mem)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . #xC7)
                  (:prefix . :any)
                  (:mod    . #b11)
                  (:reg    . #b111)
                  (:r/m    . #b000)) .
                  ("XBEGIN" 1 (J z) :1a))))

    (:Group-12 . ;; Covers opcode 0F 71.
               ((((:opcode . (#x0F #x71))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x71))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x71))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("PSRLW" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x71))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("VPSRLW" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x71))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x71))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("PSRAW" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x71))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("VPSRAW" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x71))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x71))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("PSLLW" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x71))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("VPSLLW" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x71))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (:none))))

    (:Group-13 . ;; Covers opcode 0F 72.
               ((((:opcode . (#x0F #x72))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x72))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x72))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("PSRLD" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x72))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("VPSRLD" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x72))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x72))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("PSRAD" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x72))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("VPSRAD" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x72))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x72))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("PSLLD" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x72))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("VPSLLD" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x72))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (:none))))

    (:Group-14 . ;; Covers opcode 0F 73.
               ((((:opcode . (#x0F #x73))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x73))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x73))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("PSRLQ" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x73))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("VPSRLQ" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x73))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("VPSRLDQ" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x73))
                  (:prefix . :none)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x73))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (#x0F #x73))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("PSLLQ" 2 (N q) (I b) :1a))
                (((:opcode . (#x0F #x73))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("VPSLLQ" 3 (H x) (U x) (I b) :1a))
                (((:opcode . (#x0F #x73))
                  (:prefix . :66)
                  (:mod    . #b11)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("VPSLLDQ" 3 (H x) (U x) (I b) :1a))))

    (:Group-15 . ;; Covers opcode 0F AE.
               ((((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . :mem)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("FXSAVE" 0 :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :F3)
                  (:mod    . #b11)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("RDFSBASE" 1 (R y) :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . :mem)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("FXRSTOR" 0 :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :F3)
                  (:mod    . #b11)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("RDGSBASE" 1 (R y) :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . :mem)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("LDMXCSR" 0 :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :F3)
                  (:mod    . #b11)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("WRFSBASE" 1 (R y) :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . :mem)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("STMXCSR" 0 :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :F3)
                  (:mod    . #b11)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("WRGSBASE" 1 (R y) :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . :mem)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("XSAVE" 0 :1a))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (("XRSTOR" 0 :1a)
                   ("LFENCE" 0 :1a)))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (("XSAVEOPT" 0 :1a)
                   ("MFENCE" 0 :1a)))
                (((:opcode . (#x0F #xAE))
                  (:prefix . :none)
                  (:mod    . #b11)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (("CLFLUSH" 0 :1a)
                   ("SFENCE"  0 :1a)))))

    (:Group-16 . ;; Covers opcode 0F 18.
               ((((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :mem)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  ("PREFETCHNTA" 0 :1a))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :mem)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("PREFETCHT0" 0 :v))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :mem)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("PREFETCHT1" 0 :1a))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :mem)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("PREFETCHT2" 0 :1a))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  ("RESERVEDNOP" 0))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  ("RESERVEDNOP" 0))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  ("RESERVEDNOP" 0))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  ("RESERVEDNOP" 0))
                (((:opcode . (#x0F #x18))
                  (:prefix . :any)
                  (:mod    . #b11)
                  (:reg    . :any)
                  (:r/m    . :any)) .
                  ("RESERVEDNOP" 0))))

    (:Group-17 . ;; Covers opcode VEX 0F 38 F3.
               ((((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b000)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b001)
                  (:r/m    . :any)) .
                  ("BLSR" 2 (B y) (E y) :v))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b010)
                  (:r/m    . :any)) .
                  ("BLSMSK" 2 (B y) (E y) :v))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b011)
                  (:r/m    . :any)) .
                  ("BLSI" 2 (B y) (E y) :v))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b100)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b101)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b110)
                  (:r/m    . :any)) .
                  (:none))
                (((:opcode . (:vex #x0F #x38 #xF3))
                  (:prefix . :any)
                  (:mod    . :any)
                  (:reg    . #b111)
                  (:r/m    . :any)) .
                  (:none))))
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
;; following are the allowed KEYS:
;;     :NO-PREFIX, :66, :F3, :F2, and all superscripts in
;;     *opcode-map-true-superscripts*.
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

;; TODO: What do I do about the opcode extensions (which will have a
;; different recognizer than the opcode maps one), esp. stuff like the
;; following:
;; (("XRSTOR" 0 :1a)
;;  ("LFENCE" 0 :1a))

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
   :VEX2-BYTE0))

(defconst *simple-cells-legal-keywords*
  (append
   ;; Semantics of :ALT:
   ;; Consider the following:
   ;; (:66 . (:ALT .
   ;;               (("VPEXTRB"    3 (R d)  (V dq)  (I b))
   ;;                ("VPEXTRB"    3 (M b)  (V dq)  (I b)))))
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
       (rest (cdr cell)))
    (and (or (stringp first)
             (member-equal first *group-numbers*))
         (simple-cell-addressing-info-p rest)))
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
           (rest (cdr cell)))
        (cond ((equal first :ALT)
               (basic-simple-cells-p rest))
              ((member-equal first *simple-cells-standalone-legal-keywords*)
               (equal rest nil))
              (t nil))))
  ///
  (defthm simple-cell-p-implies-true-listp
    (implies (simple-cell-p cell)
             (true-listp cell))
    :rule-classes :forward-chaining))

(defconst *mandatory-prefixes*
  '(:66 :F3 :F2))

(defconst *compound-cells-legal-keys*
  (append
   (list :NO-PREFIX)
   *mandatory-prefixes*
   *opcode-map-true-superscripts*))

(define compound-cells-legal-key-p (k)
  (if (true-listp k)
      ;; We can have more than one mandatory prefix: e.g.: in the
      ;; *0F-38-three-byte-opcode-map-lst*:
      ;; ((:66 :F2) . ("CRC32" 2 (G d) (E b)))
      (subsetp-equal k *mandatory-prefixes*)
    (member-equal k *compound-cells-legal-keys*)))

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

(local
 (define len-of-each-row-okay-p ((x true-list-listp))
   (if (endp x)
       t
     (and (equal (len (car x)) 16)
          (len-of-each-row-okay-p (cdr x))))))

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

;; ----------------------------------------------------------------------

;; Some interesting resources related to x86 ISA instruction encoding:

;; -- https://www.strchr.com/machine_code_redundancy

;; -- http://www.mlsite.net/blog/?p=76

;; -- http://www.mlsite.net/8086/#tbl_map1 --- this corresponds to
;;    Intel Manuals v24319102, which date back to 1999
;;    (http://datasheets.chipdb.org/Intel/x86/Intel%20Architecture/24319102.pdf).

;; ----------------------------------------------------------------------
