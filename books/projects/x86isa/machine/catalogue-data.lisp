; x86isa categorized listings of implemented/unimplemented instructions
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

(in-package "X86ISA")

(include-book "catalogue-base")

(local (in-theory (disable inst-list-p-of-maps)))

(def-sdm-instruction-section "5.1 General-Purpose Instructions")
(def-sdm-instruction-section "5.1.1 Data Transfer Instructions"
  :mnemonics
  '(MOV
    CMOVE/Z  CMOVNE/NZ  CMOVA/NBE CMOVAE/NB/NC CMOVB/C/NAE
    CMOVBE/NA CMOVNLE/G CMOVNL/GE  CMOVL/NGE CMOVLE/NG
    CMOVP/PE
    CMOVNP/PO
    CMOVO CMOVNO CMOVS CMOVNS  XCHG
    BSWAP XADD CMPXCHG CMPXCHG8B PUSH |PUSH CS| |PUSH DS| |PUSH ES| |PUSH FS| |PUSH GS| |PUSH SS|
    POP |POP DS| |POP ES| |POP SS| PUSHA/PUSHAD POPA/POPAD CWD/CDQ/CQO
    CBW/CWDE/CDQE MOVSX MOVZX
    ;; not listed but seems to belong here?
    MOVSXD)
  :doc "<p>Unimplemented instructions are:</p>
<ul>
<li>POP variants that write to segment registers: these have side effects,
perhaps similar to those of MOV to a segment register</li>
<li>CMPEXCHG8B</li>
</ul>")

(def-sdm-instruction-section "5.1.2 Binary Arithmetic Instructions"
  :mnemonics
  '(ADCX ADOX ADD ADC SUB SBB IMUL MUL IDIV DIV INC DEC NEG CMP)
  :doc "<p>The only unimplemented instructions are ADCX and ADOX, which set
  CF and OF flags differently from the more typical ADD/ADC operations.</p>")

(def-sdm-instruction-section "5.1.3 Decimal Arithmetic Instructions"
  :mnemonics
  '(DAA DAS AAA AAS AAM AAD)
  :doc "<p>These are all unimplemented.</p>")

(def-sdm-instruction-section "5.1.4 Logical Instructions"
  :mnemonics '(AND OR XOR NOT))

(def-sdm-instruction-section "5.1.5 Shift and Rotate Instructions"
  :mnemonics '(SAR SHR SHL/SAL SHRD SHLD ROR ROL RCR RCL))

(def-sdm-instruction-section "5.1.6 Bit and Byte Instructions"
  :mnemonics '(BT BTS BTR BTC BSF BSR
                  SETB/NAE/C SETNB/AE/NC SETNBE/A SETP/PE SETNP/PO SETL/NGE
                  SETNL/GE SETLE/NG SETNLE/G SETZ/E SETNZ/NE SETBE/NA
                  SETS SETNS SETO SETNO  TEST CRC32 POPCNT)
  :doc "<p>Unimplemented instructions are:</p>
<ul>
<li>POPCNT</li>
<li>BTC</li>
<li>CRC32</li>
</ul>")

(def-sdm-instruction-section "5.1.7 Control Transfer Instructions"
  :mnemonics '(JMP JB/NAE/C JNB/AE/NC JZ/E JNZ/NE JBE/NA JNBE/A JP/PE JNP/PO JL/NGE
                   JNL/GE JLE/NG JNLE/G |JrCXZ|
                   LOOPNE/LOOPNZ LOOPE/LOOPZ CALL IRET/D/Q
                   JO JNO JS JNS LOOP RET INT INT1 INT3 INTO BOUND ENTER LEAVE)
  :doc "<p>Unimplemented instructions are:</p>
<ul>
<li>BOUND -- not valid in 64 bit mode</li>
<li>ENTER</li>
<li>RET -- only far return with immediate (0xCA)</li>
<li>INT -- software interrupt</li>
<li>INTO -- overflow trap</li>
<li>JMP (0xEA) -- Jump far, absolute indirect (invalid in 64 bit mode)</li>
</ul>")

(def-sdm-instruction-section "5.1.8 String Instructions"
  :mnemonics '(MOVS/B MOVS/W/D/Q
                      CMPS/B CMPS/W/D
                      STOS/B STOS/W/D/Q
                      SCAS/B SCAS/W/D/Q
                      LODS/B LODS/W/D/Q
                      ;; note: these are prefixes, not defined as such
                      ;; in inst-listing their mnemonics are :prefix-rep/repe
                      ;; and :prefix-repne
                      ;; REP
                      ;; REPE/REPZ
                      ;; REPNE/REPNZ
                      )
  :doc "<p>Unimplemented instructions: SCAS and LODS variations. Note: the
  SDM includes the REP(E/NE/Z/ZE) prefixes in this section, but since these
  are prefixes rather than standalone instructions I can't automatically check
  whether they're supported. It looks like they are for MOVS/CMPS/STOS.</p>")

(def-sdm-instruction-section "5.1.9 I/O Instructions"
  :mnemonics '(IN
               OUT
               INS/INSB
               INS/INSW/INSD
               OUTS/OUTSB
               OUTS/OUTSW/OUTSD)
  :doc "<p>These are unimplemented. The only one that currently has a function is
  OUT (0xE6), which is used for printing; see @(see x86-out) and @(see
  modelcalls).</p>")

(def-sdm-instruction-section "5.1.10 Enter and Leave Instructions"
  :mnemonics '(ENTER LEAVE)
  :doc "<p>This group just includes ENTER and LEAVE, which oddly are also
  counted amongst the @(see |5.1.7 Control Transfer Instructions|) group. LEAVE
  is defined but ENTER is not.</p>")

(def-sdm-instruction-section "5.1.11 Flag Control (EFLAG) Instructions"
  :mnemonics '(STC CLC CMC CLD STD LAHF SAHF PUSHF/D/Q POPF/D/Q STI CLI))

(def-sdm-instruction-section "5.1.12 Segment Register Instructions"
  :mnemonics '(LDS LES LFS LGS LSS)
  :doc "<p>None of these are implemented</p>")

(def-sdm-instruction-section "5.1.13 Miscellaneous Instructions"
  :mnemonics '(
               LEA NOP UD1 UD2 ;; UD0 ??
               XLAT/XLATB CPUID MOVBE |prefetchw(/1)|
               ;; PREFETCHWT1
               CLFLUSH
               ;; CLFLUSHOPT
               )
  :doc "<p>Unimplemented instructions are:</p>
<ul>
<li>XLAT: table lookup in memory</li>
<li>PREFETCHW: prefetch with intent to write</li>
<li>CLFLUSH: flush cache line</li>
<li>MOVBE: move data after reversing byte order</li>
</ul>
<p>One oddity: Another UD operation form, UD0 (0x0FFF) is described in the
  manual but not listed in our opcode maps.</p>")

(def-sdm-instruction-section "5.1.14 User Mode Extended State Save/Restore Instructions"
  :mnemonics '(XSAVE ;; XSAVEC
               XSAVEOPT XRSTOR XGETBV)
  :doc "<p>None of these instructions are implemented.</p>
<p>Additionally, XSAVEC (0x0FC7 /4) seems to be missing from the opcode
  maps.</p>")

(def-sdm-instruction-section "5.1.15 Random Number Generator Instructions"
  :mnemonics '(RDRAND RDSEED)
  :doc "<p>This group consists of only RDRAND and RDSEED. RDRAND is implemented
  -- logically, it returns an undefined value (see @(see undef-read)),
  and in execution it produces a random number using Common Lisp's @('random').
  RDSEED is not implemented. From the manual it seems like it could be
  logically described similarly to RDRAND, but should produce \"better\" random
  numbers.</p>")

(def-sdm-instruction-section "5.1.16 BMI1 and BMI2 Instructions"
  :mnemonics '(ANDN BEXTR BLSI BLSMSK BLSR BZHI LZCNT MULX PDEP PEXT RORX SARX
                    SHLX SHRX TZCNT)
  :doc "<p>Most of these are unimplemented. Many of them are VEX encoded but
  operate on GPRs.</p>
<ul>
<li>LZCNT -- leading zero count</li>
<li>ANDN -- logical AND NOT</li>
<li>BLSI, BLSMSK, BLSR -- operations involving lowest set bit</li>
<li>BZHI -- zero bits left of an index</li>
<li>PDEP/PEXT -- bitmask deposit/extract</li>
<li>BEXTR -- bit field extract</li>
<li>MULX -- multiply without affecting flags</li>
<li>RORX -- rotate without affecting flags</li>
</ul>
<p>The ones that are implemented are TZCNT (trailing 0 count) and shifts without
  affecting flags (SARX, SHLX, SHRX).</p>")

;; (def-sdm-instruction-section "5.1.16.1 Detection of VEX-Encoded GPR Instructions, LZCNT, TZCNT, and PREFETCHW")

(def-sdm-instruction-section "5.2 X87 FPU Instructions")

(def-sdm-instruction-section "5.2.1 X87 FPU Data Transfer Instructions"
  :mnemonics '(FLD FST FSTP FILD FIST FISTP FBLD FBSTP FXCH FCMOVE FCMOVNE
                   FCMOVB FCMOVBE FCMOVNB FCMOVNBE FCMOVU FCMOVNU))
(def-sdm-instruction-section "5.2.2 X87 FPU Basic Arithmetic Instructions"
  :mnemonics
  '(FADD FADDP FIADD FSUB FSUBP FISUB FSUBR FSUBRP FISUBR FMUL FMULP FIMUL FDIV
 FDIVP FIDIV FDIVR FDIVRP FIDIVR FPREM FPREM1 FABS FCHS FRNDINT FSCALE FSQRT
 FXTRACT))

(def-sdm-instruction-section "5.2.3 X87 FPU Comparison Instructions"
  :mnemonics
  '(FCOM FCOMP FCOMPP FUCOM FUCOMP FUCOMPP FICOM FICOMP FCOMI FUCOMI FCOMIP
 FUCOMIP FTST FXAM))

(def-sdm-instruction-section "5.2.4 X87 FPU Transcendental Instructions"
  :mnemonics
  '(FSIN FCOS FSINCOS FPTAN FPATAN F2XM1 FYL2X FYL2XP1))

(def-sdm-instruction-section "5.2.5 X87 FPU Load Constants Instructions"
  :mnemonics
  '(FLD1 FLDZ FLDPI FLDL2E FLDLN2 FLDL2T FLDLG2))

(def-sdm-instruction-section "5.2.6 X87 FPU Control Instructions"
  :mnemonics
  '(FINCSTP FDECSTP FFREE ;; FINIT
            FNINIT        ;; FCLEX
            FNCLEX        ;; FSTCW
            FNSTCW FLDCW  ;; FSTENV
            FNSTENV FLDENV ;; FSAVE
            FNSAVE FRSTOR  ;; FSTSW
            FNSTSW FWAIT/WAIT FNOP)
  :doc "
<p>Note a few of X86 control instructions are listed in the SDM as being
encoded using 0x9B as a prefix. This is a bit weird since 9B is also an opcode
on its own, FWAIT/WAIT. It seems as though the behavior of these 9B-prefixed
instructions is basically to wait for exceptions and then (if no exception) do
what the instruction. Not sure why they are listed that way.</p>")

(def-sdm-instruction-section "5.3 X87 FPU and SIMD State Management Instructions"
  :mnemonics '(FXSAVE FXRSTOR))

(def-sdm-instruction-section "5.4 MMX Instructions")
(def-sdm-instruction-section "5.4.1 MMX Data Transfer Instructions"
  :mnemonics '(MOVD/Q MOVQ)
  :features :mmx
  :doc "<p>MMX versions of these instructions are not implemented</p>")

(def-sdm-instruction-section "5.4.2 MMX Conversion Instructions"
  :mnemonics '(PACKSSWB PACKSSDW PACKUSWB PUNPCKHBW PUNPCKHWD PUNPCKHDQ PUNPCKLBW PUNPCKLWD PUNPCKLDQ)
  :features :mmx
  :doc "<p>All unimplemented</p>")

(def-sdm-instruction-section "5.4.3 MMX Packed Arithmetic Instructions"
  :mnemonics '(PADDB PADDW PADDD PADDSB PADDSW PADDUSB PADDUSW PSUBB PSUBW
                     PSUBD PSUBSB PSUBSW PSUBUSB PSUBUSW PMULHW PMULLW PMADDWD)
  :features '(or :mmx (and :sse "PMULHW"))
  :doc "<p>MMX versions are all unimplemented. A few have SSE versions
  implemented.</p>")

(def-sdm-instruction-section "5.4.4 MMX Comparison Instructions"
  :mnemonics '(PCMPEQB PCMPEQW PCMPEQD PCMPGTB PCMPGTW PCMPGTD)
  :features :mmx
  :doc "<p>MMX versions are all unimplemented.</p>")
(def-sdm-instruction-section "5.4.5 MMX Logical Instructions"
  :mnemonics '(PAND PANDN POR PXOR)
  :features :mmx
  :doc "<p>MMX versions are all unimplemented.</p>")

(def-sdm-instruction-section "5.4.6 MMX Shift and Rotate Instructions"
  :mnemonics '(PSLLW PSLLD PSLLQ PSRLW PSRLD PSRLQ PSRAW PSRAD)
  :features :mmx
  :doc "<p>MMX versions are all unimplemented.</p>")

(def-sdm-instruction-section "5.4.7 MMX State Management Instructions"
  :mnemonics '(EMMS)
  :doc "<p>Unimplemented</p>")

(def-sdm-instruction-section "5.5 Intel(R) SSE Instructions")
(def-sdm-instruction-section "5.5.1 Intel(R) SSE SIMD Single Precision Floating-Point Instructions")
(def-sdm-instruction-section "5.5.1.1 Intel(R) SSE Data Transfer Instructions"
  :mnemonics '(MOVAPS MOVUPS MOVHPS MOVHLPS MOVLPS MOVLHPS MOVMSKPS MOVSS)
  ;; :features :sse
  :doc "<p>Unimplemented:</p>
<ul>
<li>MOVLHPS</li>
<li>MOVMSKPS</li>
</ul>
")

(def-sdm-instruction-section "5.5.1.2 Intel(R) SSE Packed Arithmetic Instructions"
  :mnemonics '(ADDPS ADDSS SUBPS SUBSS MULPS MULSS DIVPS DIVSS RCPPS RCPSS
                     SQRTPS SQRTSS RSQRTPS RSQRTSS MAXPS MAXSS MINPS MINSS)
  :features :sse
  :doc "<p>Unimplemented: RSQRTPS, RSQRTSS, RCPPS, RCPSS</p>")

(def-sdm-instruction-section "5.5.1.3 Intel(R) SSE Comparison Instructions"
  :mnemonics '(CMPPS CMPSS COMISS UCOMISS)
  :features :sse)

(def-sdm-instruction-section "5.5.1.4 Intel(R) SSE Logical Instructions"
  :mnemonics '(ANDPS ANDNPS ORPS XORPS)
  :features :sse)

(def-sdm-instruction-section "5.5.1.5 Intel(R) SSE Shuffle and Unpack Instructions"
  :mnemonics '(SHUFPS UNPCKHPS UNPCKLPS)
  :features :sse)

(def-sdm-instruction-section "5.5.1.6 Intel(R) SSE Conversion Instructions"
  :mnemonics '(CVTPI2PS CVTSI2SS CVTPS2PI CVTTPS2PI CVTSS2SI CVTTSS2SI)
  :features :sse)

(def-sdm-instruction-section "5.5.2 Intel(R) SSE MXCSR State Management Instructions"
  :mnemonics '(LDMXCSR STMXCSR)
  ;; :features :sse
  )

(def-sdm-instruction-section "5.5.3 Intel(R) SSE 64-Bit SIMD Integer Instructions"
  :mnemonics '(PAVGB PAVGW PEXTRW PINSRW PMAXUB PMAXSW PMINUB PMINSW PMOVMSKB PMULHUW PSADBW PSHUFW)
  :features :sse
  :doc "<p>None of these are implemented.</p>")

(def-sdm-instruction-section "5.5.4 Intel(R) SSE Cacheability Control, Prefetch, and Instruction Ordering Instructions"
  :mnemonics '(;; PREFETCHIT0 PREFETCHIT1
               MASKMOVQ MOVNTQ MOVNTPS PREFETCHT0 PREFETCHT1 PREFETCHT2 PREFETCHNTA SFENCE)
  :doc "<p>Unimplemented: MOVNTPS, SFENCE, MOVNTQ, MASKMOVQ.</p>
<p>Implemented instructions (PREFETCHNTA, PREFETCHT0, PREFETCHT1, PREFETCHT2) are no-ops.</p>
<p>Possible bugs:</p>
<ul>
<li>SFENCE lists SSE feature which (perhaps oddly) isn't present in SDM</li>
</ul>")

(def-sdm-instruction-section "5.6 Intel(R) SSE2 Instructions")
(def-sdm-instruction-section "5.6.1 Intel(R) SSE2 Packed and Scalar Double Precision Floating-Point Instructions")
(def-sdm-instruction-section "5.6.1.1 Intel(R) SSE2 Data Movement Instructions"
  :mnemonics '(MOVAPD MOVUPD MOVHPD MOVLPD MOVMSKPD MOVSD)
  :features :sse2
  :doc "<p>Unimplemented: MOVMSKPD</p>")
(def-sdm-instruction-section "5.6.1.2 Intel(R) SSE2 Packed Arithmetic Instructions"
  :mnemonics '(ADDPD ADDSD SUBPD SUBSD MULPD MULSD DIVPD DIVSD SQRTPD SQRTSD MAXPD MAXSD MINPD MINSD)
  :features :sse2)

(def-sdm-instruction-section "5.6.1.3 Intel(R) SSE2 Logical Instructions"
  :mnemonics '(ANDPD ANDNPD ORPD XORPD)
  :features :sse2)

(def-sdm-instruction-section "5.6.1.4 Intel(R) SSE2 Compare Instructions"
  :mnemonics '(CMPPD CMPSD COMISD UCOMISD)
  :features :sse2)

(def-sdm-instruction-section "5.6.1.5 Intel(R) SSE2 Shuffle and Unpack Instructions"
  :mnemonics '(SHUFPD UNPCKHPD UNPCKLPD)
  :features :sse2)

(def-sdm-instruction-section "5.6.1.6 Intel(R) SSE2 Conversion Instructions"
  :mnemonics '(CVTPD2PI CVTTPD2PI CVTPI2PD CVTPD2DQ CVTTPD2DQ CVTDQ2PD CVTPS2PD CVTPD2PS
                        CVTSS2SD CVTSD2SS CVTSD2SI CVTTSD2SI CVTSI2SD)
  :features '(or :sse2 (and (or "CVTPI2PD" "CVTTPD2PI" "CVTPD2PI") :mmx))
  :doc "<p>Unimplemented: CVT(T)PD2PI, CVT(T)PD2DQ, CVTPI2PD, CVTDQ2PD, i.e., the
packed integer-float and float-integer converts. Scalar integer-float and
float-integer are implemented as are scalar and packed float-float.</p>")

(def-sdm-instruction-section "5.6.2 Intel(R) SSE2 Packed Single Precision Floating-Point Instructions"
  :mnemonics '(CVTDQ2PS CVTPS2DQ CVTTPS2DQ)
  :features :sse2
  :doc "<p>Unimplemented</p>")

(def-sdm-instruction-section "5.6.3 Intel(R) SSE2 128-Bit SIMD Integer Instructions"
  :mnemonics '(MOVDQA MOVDQU MOVQ2DQ MOVDQ2Q PMULUDQ PADDQ PSUBQ
                      PSHUFLW PSHUFHW PSHUFD PSLLDQ PSRLDQ PUNPCKHQDQ PUNPCKLQDQ)
  :features '(or :sse2 "PSUBQ" "PMULUDQ" "PADDQ")
  :doc "<p>Unimplemented:</p>
<ul>
<li>MOVDQ2DQ, MOVDQ2Q</li>
<li>PADDQ, PSUBQ (MM register versions)</li>
<li>PMULUDQ</li>
</ul>")

(def-sdm-instruction-section "5.6.4 Intel(R) SSE2 Cacheability Control and Ordering Instructions"
  :mnemonics '(CLFLUSH LFENCE MFENCE ;; PAUSE
                       MASKMOVDQU MOVNTPD MOVNTDQ MOVNTI)
  :doc " <p>The only implemented instruction here is LFENCE which is treated as a no-op.</p>
<p>Unclear to me why CLFLUSH is listed here since it is also listed in @(see |5.1.13 Miscellaneous Instructions|).</p>
<p>Possible bugs:</p>
<ul>
<li>PAUSE is not present in opcode maps</li>
</ul>")

(def-sdm-instruction-section "5.6.10 Intel(R) SSE2 Instructions Promoted from Previous Extensions (and not listed previously)"
  :instructions
  (b* ((table (table-alist 'sdm-instruction-sect (w state)))
       (table (b* ((self (assoc-equal '(5 6 10) table)))
                (if self (remove-equal self table) table)))
       (table (sdm-instruction-table-organize table))
       (mmx-table (list (assoc-equal '(5 4) table))) ;; 5.4 -- MMX
       (sse2-table (list (assoc-equal '(5 6) table))) ;; 5.6 -- SSE2
       (sse-table (list (assoc-equal '(5 5) table))) ;; 5.5 -- SSE
       (all-sse2 (keep-insts-satisfying-feature :sse2 *all-opcode-maps*))
       (missing-sse2 (set::difference (set::mergesort all-sse2)
                                      (set::mergesort
                                       (append (sdm-instruction-table-implemented-instructions sse2-table)
                                               (sdm-instruction-table-unimplemented-instructions sse2-table)))))
       (mmx-sse-mnemonics (append (inst-list->mnemonics (sdm-instruction-table-implemented-instructions mmx-table))
                                  (inst-list->mnemonics (sdm-instruction-table-unimplemented-instructions mmx-table))
                                  (inst-list->mnemonics (sdm-instruction-table-implemented-instructions sse-table))
                                  (inst-list->mnemonics (sdm-instruction-table-unimplemented-instructions sse-table))))
       (missing-sse2-with-prev-mnemonics (find-insts-named-str (keep-strings mmx-sse-mnemonics) missing-sse2)))
    missing-sse2-with-prev-mnemonics))





(def-sdm-instruction-section "5.7 Intel(R) SSE3 Instructions")
(def-sdm-instruction-section "5.7.1 Intel(R) SSE3 x87-FP Integer Conversion Instruction"
  :mnemonics '(FISTTP))

(def-sdm-instruction-section "5.7.2 Intel(R) SSE3 Specialized 128-Bit Unaligned Data Load Instruction"
  :mnemonics '(LDDQU)
  :features :sse3
  :doc "<p>LDDQU is unimplemented</p>")

(def-sdm-instruction-section "5.7.3 Intel(R) SSE3 SIMD Floating-Point Packed ADD/SUB Instructions"
  :mnemonics '(ADDSUBPS ADDSUBPD)
  :features :sse3)

(def-sdm-instruction-section "5.7.4 Intel(R) SSE3 SIMD Floating-Point Horizontal ADD/SUB Instructions"
  :mnemonics '(HADDPS HSUBPS HADDPD HSUBPD)
  :features :sse3)

(def-sdm-instruction-section "5.7.5 Intel(R) SSE3 SIMD Floating-Point LOAD/MOVE/DUPLICATE Instructions"
  :mnemonics '(MOVSHDUP MOVSLDUP MOVDDUP)
  :features :sse3
  :doc "<p>Unimplemented: MOVSHDUP</p>")

(def-sdm-instruction-section "5.7.6 Intel(R) SSE3 Agent Synchronization Instructions"
  :mnemonics '(MONITOR MWAIT))

(def-sdm-instruction-section "5.8 Supplemental Streaming Simd Extensions 3 (SSSE3) Instructions")
(def-sdm-instruction-section "5.8.1 Horizontal Addition/Subtraction"
  :mnemonics '(PHADDW PHADDSW PHADDD PHSUBW PHSUBSW PHSUBD)
  :features :ssse3)

(def-sdm-instruction-section "5.8.2 Packed Absolute Values"
  :mnemonics '(PABSB PABSW PABSD)
  :features :ssse3)

(def-sdm-instruction-section "5.8.3 Multiply and Add Packed Signed and Unsigned Bytes"
  :mnemonics '(PMADDUBSW)
  :features :ssse3)
(def-sdm-instruction-section "5.8.4 Packed Multiply High with Round and Scale"
  :mnemonics '(PMULHRSW)
  :features :ssse3)
(def-sdm-instruction-section "5.8.5 Packed Shuffle Bytes"
  :mnemonics '(PSHUFB)
  :features :ssse3)
(def-sdm-instruction-section "5.8.6 Packed Sign"
  :mnemonics '(PSIGNB PSIGNW PSIGND)
  :features :ssse3)
(def-sdm-instruction-section "5.8.7 Packed Align Right"
  :mnemonics '(PALIGNR)
  :features :ssse3)

;; (def-sdm-instruction-section "5.9 Intel(R) SSE4 Instructions")
(def-sdm-instruction-section "5.10 Intel(R) SSE4.1 Instructions")
(def-sdm-instruction-section "5.10.1 Dword Multiply Instructions"
  :mnemonics '(PMULLD PMULDQ)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.2 Floating-Point Dot Product Instructions"
  :mnemonics '(DPPD DPPS)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.3 Streaming Load Hint Instruction"
  :mnemonics '(MOVNTDQA)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.4 Packed Blending Instructions"
  :mnemonics '(BLENDPD BLENDPS BLENDVPD BLENDVPS PBLENDVB PBLENDW)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.5 Packed Integer MIN/MAX Instructions"
  :mnemonics '(PMINUW PMINUD PMINSB PMINSD PMAXUW PMAXUD PMAXSB PMAXSD)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.6 Floating-Point Round Instructions with Selectable Rounding Mode"
  :mnemonics '(ROUNDPS ROUNDPD ROUNDSS ROUNDSD)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.7 Insertion and Extractions from XMM Registers"
  :mnemonics '(EXTRACTPS INSERTPS PINSRB PINSRD/Q PEXTRB PEXTRW PEXTRD/Q)
  :features :sse4.1)

(def-sdm-instruction-section "5.10.8 Packed Integer Format Conversions"
  :mnemonics '(PMOVSXBW PMOVZXBW PMOVSXBD PMOVZXBD PMOVSXWD PMOVZXWD
                        PMOVSXBQ PMOVZXBQ PMOVSXWQ PMOVZXWQ PMOVSXDQ PMOVZXDQ)
  :features :sse4.1)

(def-sdm-instruction-section "5.10.9 Improved Sums of Absolute Differences (SAD) for 4-Byte Blocks"
  :mnemonics '(MPSADBW)
  :features :sse4.1)

(def-sdm-instruction-section "5.10.10 Horizontal Search"
  :mnemonics '(PHMINPOSUW)
  :features :sse4.1)

(def-sdm-instruction-section "5.10.11 Packed Test"
  :mnemonics '(PTEST)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.12 Packed Qword Equality Comparisons"
  :mnemonics '(PCMPEQQ)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.13 Dword Packing With Unsigned Saturation"
  :mnemonics '(PACKUSDW)
  :features :sse4.1)

(def-sdm-instruction-section "5.11 Intel(R) SSE4.2 Instruction Set")
(def-sdm-instruction-section "5.11.1 String and Text Processing Instructions"
  :mnemonics '(PCMPESTRI PCMPESTRM PCMPISTRI PCMPISTRM)
  :features :sse4.2)
(def-sdm-instruction-section "5.11.2 Packed Comparison SIMD Integer Instruction"
  :mnemonics '(PCMPGTQ)
  :features :sse4.2)
(def-sdm-instruction-section "5.12 Intel(R) AES-NI And PCLMULQDQ"
  :mnemonics '(AESDEC AESDECLAST AESENC AESENCAST AESIMC AESKEYGENASSIST PCLMULQDQ)
  :doc "<p>AESENCLAST is misspelled AESENCAST</p>")

(def-sdm-instruction-section "5.13 Intel(R) Advanced Vector Extensions (Intel(R) AVX)"
  :doc "<p>The SDM doesn't have separate Chapter 5 sections for AVX instructions, but
rather lists them in tables 14-2 through 14-7. We create fake sections for
these, e.g., the ones listed in 14-2 are instead in fake section @(see
|5.13.14.2 Promoted 256-Bit and 128-Bit Arithmetic Intel(R) AVX Instructions|).</p>")

(def-sdm-instruction-section "5.13.14.2 Promoted 256-Bit and 128-Bit Arithmetic Intel(R) AVX Instructions"
  :mnemonics '(VSQRTPS VSQRTPD VRSQRTPS VRCPPS VADDPS VADDPD VSUBPS VSUBPD
                       VMULPS VMULPD VDIVPS VDIVPD VCVTPS2PD VCVTPD2PS VCVTDQ2PS VCVTPS2DQ VCVTTPS2DQ
                       VCVTTPD2DQ VCVTPD2DQ VCVTDQ2PD VMINPS VMINPD VMAXPS VMAXPD VHADDPD VHADDPS
                       VHSUBPD VHSUBPS VCMPPS VCMPPD VADDSUBPD VADDSUBPS VDPPS VROUNDPD VROUNDPS)
  :features '(and :avx :vex))

(def-sdm-instruction-section "5.13.14.3 Promoted 256-Bit and 128-Bit Data Movement Intel(R) AVX Instructions"
  :mnemonics '(VMOVAPS VMOVAPD VMOVDQA VMOVUPS VMOVUPD VMOVDQU VMOVMSKPS
                       VMOVMSKPD VLDDQU VMOVNTPS VMOVNTPD VMOVNTDQ VMOVNTDQA VMOVSHDUP VMOVSLDUP
                       VMOVDDUP VUNPCKHPD VUNPCKHPS VUNPCKLPD VBLENDPS VBLENDPD VSHUFPD VSHUFPS
                       VUNPCKLPS VBLENDVPS VBLENDVPD VPTEST VMOVMSKPD VMOVMSKPS VXORPS VXORPD VORPS
                       VORPD VANDNPD VANDNPS VANDPD VANDPS)
  :features '(and :avx :vex))

(def-sdm-instruction-section "5.13.14.4 256-Bit Intel(R) AVX Instruction Enhancements"
  :mnemonics '(VBROADCASTF128 VBROADCASTSD VBROADCASTSS VEXTRACTF128
                              VINSERTF128 VMASKMOVPS VMASKMOVPD VMASKMOVPS VMASKMOVPD VPERMILPD VPERMILPD
                              VPERMILPS VPERMILPS VPERM2F128 VTESTPS VTESTPD VZEROALL VZEROUPPER)
  :features '(and :avx :vex))

(def-sdm-instruction-section "5.13.14.5 Promotion of Legacy SIMD ISA to 128-Bit Arithmetic Intel(R) AVX Instructions"
  :mnemonics '(
               VCVTSI2SS VCVTSI2SD VCVTSD2SI
               VCVTTSS2SI VCVTTSD2SI VCVTSS2SI
               VCOMISD VRSQRTSS VRCPSS
               VUCOMISS VUCOMISD VCOMISS
               VADDSS VADDSD VSUBSS VSUBSD
               VMULSS VMULSD VDIVSS VDIVSD
               VSQRTSS VSQRTSD
               VCVTSS2SD VCVTSD2SS
               VMINSS VMINSD VMAXSS VMAXSD
               VPAND VPANDN VPOR VPXOR
               VPCMPGTB VPCMPGTW VPCMPGTD
               VPMADDWD VPMADDUBSW
               VPAVGB VPAVGW VPMULUDQ
               VPCMPEQB VPCMPEQW VPCMPEQD
               VPMULLW VPMULHUW VPMULHW
               VPSUBSW VPADDSW VPSADBW
               VPADDUSB VPADDUSW VPADDSB
               VPSUBUSB VPSUBUSW VPSUBSB
               VPMINUB VPMINSW
               VPMAXUB VPMAXSW
               VPADDB VPADDW VPADDD VPADDQ
               VPSUBB VPSUBW VPSUBD VPSUBQ
               VPSLLW VPSLLD VPSLLQ VPSRAW
               VPSRLW VPSRLD VPSRLQ VPSRAD
               VPHSUBW VPHSUBD VPHSUBSW
               VPHADDW VPHADDD VPHADDSW
               VPMULHRSW
               VPSIGNB VPSIGNW VPSIGND
               VPABSB VPABSW VPABSD
               VDPPD
               VPHMINPOSUW VMPSADBW
               VPMAXSB VPMAXSD VPMAXUD
               VPMINSB VPMINSD VPMINUD
               VPMAXUW VPMINUW
               VPMOVSXBW VPMOVZXBW VPMOVSXBD VPMOVZXBD VPMOVSXWD VPMOVZXWD
                        VPMOVSXBQ VPMOVZXBQ VPMOVSXWQ VPMOVZXWQ VPMOVSXDQ VPMOVZXDQ
               VPMULDQ VPMULLD
               VROUNDSD VROUNDSS
               VPCMPGTQ
               VPCMPESTRI VPCMPESTRM
               VPCMPISTRI VPCMPISTRM
               VPCLMULQDQ
               VAESDEC VAESDECLAST
               VAESENC VAESENCLAST
               VAESIMC VAESKEYGENASSIST
               )
  :features '(and (or :avx "VPMOVZXDQ") :vex)
  :doc "
<p>SDM says POPCNT is promoted as a VEX.128 encoding but this seems inaccurate</p>")

(def-sdm-instruction-section "5.13.14.6 128-Bit Intel(R) AVX Instruction Enhancement"
  :mnemonics '(VBROADCASTSS VMASKMOVPS VMASKMOVPD VMASKMOVPS VMASKMOVPD
                            VPERMILPD VPERMILPD VPERMILPS VPERMILPS VTESTPS VTESTPD)
  :features '(and :avx :vex))

(def-sdm-instruction-section "5.13.14.7 Promotion of Legacy SIMD ISA to 128-Bit Non-Arithmetic Intel(R) AVX instruction"
  :mnemonics '(
               VLDMXCSR VSTMXCSR
               VMOVSS VMOVSD VCMPSS VCMPSD
               VMOVHPS VMOVHPD
               VMOVLPS VMOVLPD
               VMOVLHPS VMOVHLPS
               VMOVQ VMOVD
               VPACKUSWB VPACKSSDW VPACKSSWB
               VPUNPCKHBW VPUNPCKHWD
               VPUNPCKLBW VPUNPCKLWD
               VPUNPCKHDQ VPUNPCKLDQ
               VPUNPCKLQDQ VPUNPCKHQDQ
               VPSHUFHW VPSHUFLW VPSHUFD
               VPMOVMSKB VMASKMOVDQU
               VPAND VPANDN VPOR VPXOR
               VPINSRW VPEXTRW
               VPALIGNR VPSHUFB
               VEXTRACTPS VINSERTPS
               VPACKUSDW VPCMPEQQ
               VPBLENDVB VPBLENDW
               VPEXTRW VPEXTRB VPEXTRD VPEXTRQ
               VPINSRB VPINSRD VPINSRQ
               ;; not listed:
               VPSLLDQ VPSRLDQ)
  :features '(and :avx :vex))


(def-sdm-instruction-section "5.14 16-Bit Floating-Point Conversion"
  :mnemonics '(VCVTPH2PS VCVTPS2PH)
  :features :vex)

(def-sdm-instruction-section "5.15 Fused-Multiply-Add (FMA)"
  :mnemonics '(VFMADD132PD VFMADD213PD VFMADD231PD
               VFMADD132PS VFMADD213PS VFMADD231PS
               VFMADD132SD VFMADD213SD VFMADD231SD
               VFMADD132SS VFMADD213SS VFMADD231SS
               VFMADDSUB132PD VFMADDSUB213PD VFMADDSUB231PD
               VFMADDSUB132PS VFMADDSUB213PS VFMADDSUB231PS
               VFMSUBADD132PD VFMSUBADD213PD VFMSUBADD231PD
               VFMSUBADD132PS VFMSUBADD213PS VFMSUBADD231PS
               VFMSUB132PD VFMSUB213PD VFMSUB231PD
               VFMSUB132PS VFMSUB213PS VFMSUB231PS
               VFMSUB132SD VFMSUB213SD VFMSUB231SD
               VFMSUB132SS VFMSUB213SS VFMSUB231SS
               VFNMADD132PD VFNMADD213PD VFNMADD231PD
               VFNMADD132PS VFNMADD213PS VFNMADD231PS
               VFNMADD132SD VFNMADD213SD VFNMADD231SD
               VFNMADD132SS VFNMADD213SS VFNMADD231SS
               VFNMSUB132PD VFNMSUB213PD VFNMSUB231PD
               VFNMSUB132PS VFNMSUB213PS VFNMSUB231PS
               VFNMSUB132SD VFNMSUB213SD VFNMSUB231SD
               VFNMSUB132SS VFNMSUB213SS VFNMSUB231SS)
  :features :vex)

(def-sdm-instruction-section "5.16 Intel(R) Advanced Vector Extensions 2 (Intel(R) AVX2)"
  :doc "<p>The SDM doesn't have separate Chapter 5 sections for AVX2 instructions, but
rather lists them in tables 14-18 and 14-19. We create fake sections for
these.</p>")

(def-sdm-instruction-section "5.16.14.18 Promoted Vector Integer SIMD Instructions in Intel(R) AVX2"
  :mnemonics '(VPUNPCKLBW VPUNPCKLWD VPUNPCKLDQ VPACKSSWB VPCMPGTB VPCMPGTW
 VPCMPGTD VPACKUSWB VPUNPCKHBW VPUNPCKHWD VPUNPCKHDQ VPACKSSDW VPUNPCKLQDQ
 VPUNPCKHQDQ VPSHUFD VPSHUFHW VPSHUFLW VPCMPEQB VPCMPEQW VPCMPEQD VPSRLW VPSRLD
 VPSRLQ VPADDQ VPMULLW VPMOVMSKB VPSUBUSB VPSUBUSW VPMINUB VPAND VPADDUSB
 VPADDUSW VPMAXUB VPANDN VPAVGB VPSRAW VPSRAD VPAVGW VPMULHUW VPMULHW VPSUBSB
 VPSUBSW VPMINSW VPOR VPADDSB VPADDSW VPMAXSW VPXOR VPSLLW VPSLLD VPSLLQ
 VPMULUDQ VPMADDWD VPSADBW VPSUBB VPSUBW VPSUBD VPSUBQ VPADDB VPADDW VPADDD
 VPHADDW VPHADDSW VPHADDD VPHSUBW VPHSUBSW VPHSUBD VPMADDUBSW VPALIGNR VPSHUFB
 VPMULHRSW VPSIGNB VPSIGNW VPSIGND VPABSB VPABSW VPABSD VMOVNTDQA VMPSADBW
 VPACKUSDW VPBLENDVB VPBLENDW VPCMPEQQ VPMAXSB VPMAXSD VPMAXUD VPMAXUW VPMINSB
 VPMINSD VPMINUD VPMINUW
 VPMOVSXBW VPMOVZXBW VPMOVSXBD VPMOVZXBD VPMOVSXWD VPMOVZXWD
 VPMOVSXBQ VPMOVZXBQ VPMOVSXWQ VPMOVZXWQ VPMOVSXDQ VPMOVZXDQ
 VPMULDQ VPMULLD VPCMPGTQ
 ;; not listed:
 VPSLLDQ VPSRLDQ)
  :features '(and :vex-256 (or :avx2 "VPMINUB" "VPMAXUB" "VPMINSW")))

(def-sdm-instruction-section "5.16.14.19 VEX-Only SIMD Instructions in Intel(R) AVX2"
  :mnemonics '(VBROADCASTI128 VBROADCASTSD VBROADCASTSS VEXTRACTI128
                              VINSERTI128 VPMASKMOVD VPMASKMOVQ VPERM2I128 VPERMD VPERMPS VPERMQ VPERMPD
                              VPBLENDD VPSLLVD VPSLLVQ VPSRAVD VPSRLVD VPSRLVQ VGATHERDPD VGATHERQPD
                              VGATHERDPS VGATHERQPS VPGATHERDD VPGATHERQD VPGATHERDQ VPGATHERQQ
                              ;; not listed in SDM section
                              VPBROADCASTB VPBROADCASTW VPBROADCASTD VPBROADCASTQ)
  :features :avx2)


(def-sdm-instruction-section "5.17 Intel(R) Transactional Synchronization Extensions (Intel(R) Tsx)"
  :mnemonics '(XABORT
               ;; XACQUIRE
               ;; XRELEASE
               XBEGIN
               XEND
               XTEST
               ;; XRESLDTRK
               ;; XSUSLDTRK
               )
  :doc "<p>Missing opcode map entries: XAQUIRE, XRELEASE, XRESLDTRK, XSUSLDTRK</p>")

(def-sdm-instruction-section "5.18 Intel(R) SHA Extensions"
  :mnemonics '(SHA1MSG1 SHA1MSG2 SHA1NEXTE SHA1RNDS4 SHA256MSG1 SHA256MSG2 SHA256RNDS2))

(def-sdm-instruction-section "5.19 Intel(R) Advanced Vector Extensions 512 (Intel(R) AVX-512)"
  :doc "<p>This section's instruction list is divided into several subheadings; we add
subsections for them even though they aren't formally listed as subsections in
the SDM.</p>")

(def-sdm-instruction-section "5.19.1 AVX-512F instructions that are not Intel AVX or AVX2 promotions"
  :mnemonics '(
               VALIGND VALIGNQ
               VBLENDMPD VBLENDMPS
               VCOMPRESSPD VCOMPRESSPS
               VCVTTPD2UDQ VCVTPD2UDQ
               VCVTTPS2UDQ VCVTPS2UDQ
               ;; VCVTQQ2PD VCVTQQ2PS ;; actually avx512dq
               VCVTTSD2USI VCVTSD2USI
               VCVTTSS2USI VCVTSS2USI
               VCVTUDQ2PD VCVTUDQ2PS
               VCVTUSI2SD VCVTUSI2SS
               VEXPANDPD VEXPANDPS
               VEXTRACTF32X4 VEXTRACTF64X4
               VEXTRACTI32X4 VEXTRACTI64X4
               VFIXUPIMMPD VFIXUPIMMPS
               VFIXUPIMMSD VFIXUPIMMSS
               VGETEXPPD VGETEXPPS
               VGETEXPSD VGETEXPSS
               VGETMANTPD VGETMANTPS
               VGETMANTSD VGETMANTSS
               VINSERTF32X4 VINSERTF64X4
               VINSERTI32X4 VINSERTI64X4
               VMOVDQA32 VMOVDQA64
               VMOVDQU32 VMOVDQU64
               VPBLENDMD VPBLENDMQ
               VPBROADCASTD VPBROADCASTQ ;; but these do seem to be AVX2 promotions?
               VPCMPD VPCMPUD
               VPCMPQ VPCMPUQ
               VPCOMPRESSQ VPCOMPRESSD
               VPERMI2D VPERMI2Q
               VPERMI2PD VPERMI2PS
               VPERMT2D VPERMT2Q
               VPERMT2PD VPERMT2PS
               VPEXPANDD VPEXPANDQ
               VPMAXSQ
               VPMAXUD VPMAXUQ
               VPMINSQ
               VPMINUD VPMINUQ
               VPMOVSQB VPMOVUSQB VPMOVQB
               VPMOVSQW VPMOVUSQW VPMOVQW
               VPMOVSQD VPMOVUSQD VPMOVQD
               VPMOVSDB VPMOVUSDB VPMOVDB
               VPMOVSDW VPMOVUSDW VPMOVDW
               VPROLD VPROLQ
               VPROLVD VPROLVQ
               VPRORD VPRORQ
               VPRORVD VPRORVQ
               VPSCATTERDD VPSCATTERDQ
               VPSCATTERQD VPSCATTERQQ
               VPSRAQ
               VPSRAVQ
               VPTESTNMD VPTESTNMQ
               VPTERNLOGD VPTERNLOGQ
               VPTESTMD VPTESTMQ
               VRCP14PD VRCP14PS
               VRCP14SD VRCP14SS
               VRNDSCALEPD VRNDSCALEPS
               VRNDSCALESD VRNDSCALESS
               VRSQRT14PD VRSQRT14PS
               VRSQRT14SD VRSQRT14SS
               VSCALEFPD VSCALEFPS
               VSCALEFSD VSCALEFSS
               VSCATTERDPS VSCATTERDPD
               VSCATTERQPS VSCATTERQPD
               VSHUFF32X4 VSHUFF64X2
               VSHUFI32X4 VSHUFI64X2
               ;; added:
               VPABSQ)
  :features :avx512f)

(local (define get-sub-table ((section nat-listp)
                              (table sdm-instruction-table-p))
         :returns (subtable sdm-instruction-table-p)
         :prepwork ((local (defthm assoc-equal-of-sdm-instruction-table-is-hons-assoc-equal
                             (implies (sdm-instruction-table-p x)
                                      (equal (assoc-equal key x)
                                             (hons-assoc-equal key x))))))
         (b* ((look (assoc-equal section (sdm-instruction-table-fix table))))
           (and look (list look)))))

(local (define get-promoted-avx512-insts ((section nat-listp)
                                          (feature symbolp)
                                          (table sdm-instruction-table-p))
         (b* ((table (b* ((self (assoc-equal section table)))
                       (if self (remove-equal self table) table)))
              (table (sdm-instruction-table-organize table))
              (avx-tables (append (get-sub-table '(5 13) table) ;; 5.13 -- AVX
                                  (get-sub-table '(5 15) table) ;; 5.15 -- FMA
                                  (get-sub-table '(5 16) table))) ;; 5.16 -- AVX2
              (avx512-table (get-sub-table '(5 19) table)) ;; 5.19 -- avx512
              (all-feature (keep-insts-satisfying-feature feature (all-opcode-maps)))
              (feature-missing
               (set::difference (set::mergesort all-feature)
                                (set::mergesort
                                 (append (sdm-instruction-table-implemented-instructions avx512-table)
                                         (sdm-instruction-table-unimplemented-instructions avx512-table)))))
              (avx-mnemonics (append (inst-list->mnemonics (sdm-instruction-table-implemented-instructions avx-tables))
                                     (inst-list->mnemonics (sdm-instruction-table-unimplemented-instructions avx-tables))))
              (missing-with-prev-mnemonics (find-insts-named-str (keep-strings avx-mnemonics) feature-missing)))
           missing-with-prev-mnemonics)))

(def-sdm-instruction-section "5.19.2 AVX-512F instructions that are Intel AVX or AVX2 promotions"
  :instructions (get-promoted-avx512-insts '(5 19 2) :avx512f (table-alist 'sdm-instruction-sect (w state)))
  :mnemonics '(VBROADCASTF32X4
               VBROADCASTF64X4
               VBROADCASTI32X4
               VBROADCASTI64X4
               VPANDD VPANDQ VPANDND VPANDNQ VPORD VPORQ VPXORD VPXORQ)
  :features :avx512f)


(def-sdm-instruction-section "5.19.3 AVX-512DQ instructions that are not Intel AVX or AVX2 promotions"
  :mnemonics '(
               VCVTPD2QQ
               VCVTTPD2QQ
               VCVTPD2UQQ
               VCVTTPD2UQQ
               VCVTPS2QQ
               VCVTTPS2QQ
               VCVTPS2UQQ
               VCVTTPS2UQQ
               VCVTUQQ2PD
               VCVTUQQ2PS
               VEXTRACTF64X2
               VEXTRACTI64X2
               VEXTRACTF32X8
               VEXTRACTI32X8
               VFPCLASSPD
               VFPCLASSPS
               VFPCLASSSD
               VFPCLASSSS
               VINSERTF64X2
               VINSERTI64X2
               VINSERTF32X8
               VINSERTI32X8
               VPMOVM2D
               VPMOVM2Q
               ;; VPMOVB2M ;; actually avx512bw
               VPMOVQ2M
               VPMULLQ
               VRANGEPD
               VRANGEPS
               VRANGESD
               VRANGESS
               VREDUCEPD
               VREDUCEPS
               VREDUCESD
               VREDUCESS
               ;; incorrectly listed in SDM under avx512f
               VCVTQQ2PD VCVTQQ2PS
               ;; not present in SDM listing
               VPMOVD2M VPMOVQ2M)
  :features :avx512dq)

(def-sdm-instruction-section "5.19.4 AVX-512DQ instructions that are Intel AVX or AVX2 promotions"
  :instructions (get-promoted-avx512-insts '(5 19 4) :avx512dq (table-alist 'sdm-instruction-sect (w state)))
  :mnemonics '(VBROADCASTF32X2
               VBROADCASTF64X2
               VBROADCASTF32X8
               |VBROADCASTI32x2|
               VBROADCASTI64X2
               VBROADCASTI32X8)
  :features :avx512dq)


(def-sdm-instruction-section "5.19.5 AVX-512BW instructions that are not Intel AVX or AVX2 promotions"
  :mnemonics '(VDBPSADBW
               VMOVDQU8 VMOVDQU16
               VPBLENDMB
               VPBLENDMW
               VPBROADCASTB VPBROADCASTW
               VPCMPB VPCMPUB
               VPCMPW VPCMPUW
               VPERMW
               ;; VPERMI2B ;; actually avx512_vbmi
               VPERMI2W
               VPMOVM2B VPMOVM2W
               VPMOVB2M VPMOVW2M
               VPMOVSWB VPMOVUSWB VPMOVWB
               VPSLLVW VPSRAVW VPSRLVW
               VPTESTNMB VPTESTNMW
               VPTESTMB VPTESTMW
               ;; not listed in SDM section
               VPERMT2W)
  :features :avx512bw)

(def-sdm-instruction-section "5.19.6 AVX-512BW instructions that are Intel AVX or AVX2 promotions"
  :instructions (get-promoted-avx512-insts '(5 19 6) :avx512bw (table-alist 'sdm-instruction-sect (w state))))

(def-sdm-instruction-section "5.19.7 AVX-512CD instructions that are not Intel AVX or AVX2 promotions"
  :mnemonics '(VPBROADCASTMB2Q VPBROADCASTMW2D
               VPCONFLICTD VPCONFLICTQ
               VPLZCNTD VPLZCNTQ))

(def-sdm-instruction-section "5.19.8 AVX-512CD instructions that are Intel AVX or AVX2 promotions"
  :instructions (get-promoted-avx512-insts '(5 19 8) :avx512cd (table-alist 'sdm-instruction-sect (w state))))

(def-sdm-instruction-section "5.19.9 Opmask instructions"
  :mnemonics '(
               KADDB
               KADDW
               KADDD
               KADDQ
               KANDB
               KANDW
               KANDD
               KANDQ
               KANDNB
               KANDNW
               KANDND
               KANDNQ
               KMOVB
               KMOVW
               KMOVD
               KMOVQ
               KNOTB
               KNOTW
               KNOTD
               KNOTQ
               KORB
               KORW
               KORD
               KORQ
               KORTESTB
               KORTESTW
               KORTESTD
               KORTESTQ
               KSHIFTLB
               KSHIFTLW
               KSHIFTLD
               KSHIFTLQ
               KSHIFTRB
               KSHIFTRW
               KSHIFTRD
               KSHIFTRQ
               KTESTB
               KTESTW
               KTESTD
               KTESTQ
               KUNPCKBW
               KUNPCKWD
               KUNPCKDQ
               KXNORB
               KXNORW
               KXNORD
               KXNORQ
               KXORB
               KXORW
               KXORD
               KXORQ))

(def-sdm-instruction-section "5.19.10 AVX-512ER instructions"
  :mnemonics '(
               VEXP2PD
               VEXP2PS
               ;; VEXP2SD
               ;; VEXP2SS
               VRCP28PD
               VRCP28PS
               VRCP28SD
               VRCP28SS
               VRSQRT28PD
               VRSQRT28PS
               VRSQRT28SD
               VRSQRT28SS)
  :doc "
<p>Apparently VEXP2SD/VEXP2SS don't exist, even though they are listed in the
table in the SDM -- they are not mentioned elsewhere</p>")

(def-sdm-instruction-section "5.19.11 AVX-512PF instructions"
  :mnemonics '(VGATHERPF0DPD VGATHERPF0DPS VGATHERPF0QPD VGATHERPF0QPS
                             VGATHERPF1DPD VGATHERPF1DPS VGATHERPF1QPD VGATHERPF1QPS VSCATTERPF0DPD
                             VSCATTERPF0DPS VSCATTERPF0QPD VSCATTERPF0QPS VSCATTERPF1DPD VSCATTERPF1DPS
                             VSCATTERPF1QPD VSCATTERPF1QPS))

(def-sdm-instruction-section "5.19.12 AVX512-FP16 instructions"
  :mnemonics '(VCVTPH2PS VCVTPS2PH
 ;;               VADDPH VADDSH VCMPPH VCMPSH VCOMISH VCVTDQ2PH VCVTPD2PH
 ;; VCVTPH2DQ VCVTPH2QQ VCVTPH2PD VCVTPH2PSX VCVTPH2QQ VCVTPH2UDQ
 ;; VCVTPH2UQQ VCVTPH2UW VCVTPH2W VCVTPS2PHX VCVTQQ2PH VCVTSD2SH
 ;; VCVTSH2SD VCVTSH2SS VCVTSH2SI VCVTSH2USI VCVTSI2SH VCVTSS2SH VCVTTPH2DQ
 ;; VCVTTPH2QQ VCVTTPH2UDQ VCVTTPH2UQQ VCVTTPH2UW VCVTTPH2W VCVTTSH2SI VCVTTSH2USI
 ;; VCVTUDQ2PH VCVTUQQ2PH VCVTUSI2SH VCVTUW2PH VCVTW2PH VDIVPH VDIVSH VFMADDCPH
 ;; VFCMADDCPH VFMADDCSH VFCMADDCSH VFMULCPH VFCMULCPH VFMULCSH VFCMULCSH
 ;; VFMADD132PH VFMADD213PH VFMADD231PH VFNMADD132PH VFNMADD213PH VFNMADD231PH
 ;; VFMADD132SH VFMADD213SH VFMADD231SH VFNMADD132SH VFNMADD213SH VFNMADD231SH
 ;; VFMADDSUB132PH VFMADDSUB213PH VFMADDSUB231PH VFMSUBADD132PH VFMSUBADD213PH
 ;; VFMSUBADD231PH VFMSUB132PH VFMSUB213PH VFMSUB231PH VFNMSUB132PH VFNMSUB213PH
 ;; VFNMSUB231PH VFMSUB132SH VFMSUB213SH VFMSUB231SH VFNMSUB132SH VFNMSUB213SH
 ;; VFNMSUB231SH VFPCLASSPH VFPCLASSSH VGETEXPPH VGETEXPSH VGETMANTPH VGETMANTSH
 ;; VMAXPH VMAXSH VMINPH VMINSH VMOVSH VMOVW VMULPH VMULSH VRCPPH VRCPSH VREDUCEPH
 ;; VREDUCESH VRNDSCALEPH VRNDSCALESH VRSQRTPH VRSQRTSH VSCALEPH VSCALESH VSQRTPH
 ;; VSQRTSH VSUBPH VSUBSH VUCOMISH
                         )
  :doc "<p>As far as I understand we don't yet support EVEX MAP5 or MAP6 encodings -- I
think we basically need two new opcode maps for these.</p>")


(def-sdm-instruction-section "5.19.13 Other AVX512 Features Not Listed in SDM Ch. 5"
  :doc "<p>Organized by feature for now.</p>")

(def-sdm-instruction-section "5.19.13.1 AVX512-VBMI instructions"
  :mnemonics '(VPERMB VPERMI2B VPERMT2B
                      VPMULTISHIFTQB
                      )
  :features :avx512_vbmi)

(def-sdm-instruction-section "5.19.13.2 AVX512-VBMI2 instructions"
  ;; :mnemonics '(VPCOMPRESSB VPCOMPRESSW VPEXPANDB VPEXPANDW)
  :features :avx512_vbmi2
  :doc " <p>Missing from opcode maps</p>")

(def-sdm-instruction-section "5.19.13.3 AVX512-IFMA instructions"
  :instructions (all-opcode-maps)
  :features :avx512_ifma)

(def-sdm-instruction-section "5.19.13.4 AVX512-4FMAPS instructions"
  :instructions (all-opcode-maps)
  :features :avx512_4fmaps)

(def-sdm-instruction-section "5.19.13.5 AVX512-4VNNIW instructions"
  :instructions (all-opcode-maps)
  :features :avx512_4vnniw)




(def-sdm-instruction-section "5.20 System Instructions"
  :mnemonics '(CLAC STAC LGDT SGDT LLDT SLDT LTR STR LIDT SIDT ;; MOV
                    LMSW SMSW CLTS ARPL LAR LSL VERR VERW           ;; MOV
                    INVD WBINVD INVLPG INVPCID ;; LOCK -- a prefix
                    HLT RSM RDMSR WRMSR RDPMC RDTSC RDTSCP SYSENTER SYSEXIT XSAVE ;; XSAVEC
                    XSAVEOPT ;; XSAVES
                    XRSTOR   ;; XRSTORS
                    XGETBV XSETBV RDFSBASE RDGSBASE WRFSBASE WRGSBASE
                    )
  :doc "
<ul>
<li>XRSTORS (0x0FC7 /3) XSAVEC (0x0FC7 /4), and XSAVES (0x0FC7 /5) are missing from the opcode maps</li>
<li>Removed MOV from the list until I can specify only certain forms of it</li>
</ul>")


(def-sdm-instruction-section "5.21 64-Bit Mode Instructions"
  :mnemonics '(CBW/CWDE/CDQE CMPS/W/D CMPXCHG16B LODS/W/D/Q MOVS/W/D/Q MOVZX
                             STOS/W/D/Q SWAPGS SYSCALL SYSRET)
  :doc "
<ul>
<li>Perhaps CMPS/W/D should be called CMPS/W/D/Q</li>
</ul>")

(def-sdm-instruction-section "5.22 Virtual-Machine Extensions"
  :mnemonics '(
VMPTRLD
;; VMPTRST
VMCLEAR
MREAD ;; VMREAD
MWRITE ;; VMWRITE
VMLAUNCH
VMRESUME
VMXOFF VMXON
INVEPT
INVVPID
VMCALL
VMFUNC
)
  :doc "<ul>
<li>VMPTRST (0x0F_C7 /7) is missing from the opcode map</li>
<li>VMREAD and VMWRITE (0x0F_78 and 0x0F_79) are listed with mnemonics MREAD and MWRITE</li>
</ul>")

(def-sdm-instruction-section "5.23 Safer Mode Extensions"
  :mnemonics '(GETSEC))
(def-sdm-instruction-section "5.24 Intel(R) Memory Protection Extensions"
  :mnemonics '(BNDMK BNDCL BNDCU BNDCN BNDMOV BNDMOV BNDLDX BNDSTX))

(def-sdm-instruction-section "5.25 Intel(R) Software Guard Extensions"
  :mnemonics '(ENCLS ENCLU))
(def-sdm-instruction-section "5.26 Shadow Stack Management Instructions"
  :mnemonics nil
  ;; '(CLRSSBSY INCSSP RDSSP RSTORSSP SAVEPREVSSP SETSSBSY WRSS WRUSS)
  :doc "<p>Not yet included in opcode maps</p>")

(def-sdm-instruction-section "5.27 Control Transfer Terminating Instructions"
  :mnemonics '(ENDBR32/ENDBR64))

(def-sdm-instruction-section "5.28 Intel(R) AMX Instructions"
  :mnemonics nil
  ;; '(LDTILECFG STTILECFG TDPBF16PS TDPBSSD TDPBSUD TDPBUSD TDPBUUD
  ;;                        TILELOADD TILELOADDT1 TILERELEASE TILESTORED TILEZERO)
  :doc "<p>Not yet included in opcode maps</p>")
(def-sdm-instruction-section "5.29 User Interrupt Instructions"
  :mnemonics nil
  ;; '(CLUI SENDUIPI STUI TESTUI UIRET)
  :doc "<p>Not yet included in opcode maps</p>")
(def-sdm-instruction-section "5.30 Enqueue Store Instructions"
  :mnemonics nil
  ;; '(ENQCMD ENQCMDS)
  :doc "<p>Not yet included in opcode maps</p>")



(def-sdm-instruction-section "5.31 Intel(R) Advanced Vector Extensions 10 Version 1 Instructions")

(def-sdm-instruction-section "5.40 Other ISA Extensions"
  :mnemonics '(RDPID))


(define keep-string-mnemonic-insts ((x inst-list-p))
  :returns (insts inst-list-p)
  (if (atom x)
      nil
    (if (stringp (inst->mnemonic (car x)))
        (cons (inst-fix (car x))
              (keep-string-mnemonic-insts (cdr x)))
      (keep-string-mnemonic-insts (cdr x)))))


(def-sdm-instruction-section "5.50 Uncategorized \"Instructions\""
  :instructions
  (b* ((section '(5 50))
       (table (table-alist 'sdm-instruction-sect (w state)))
       (self (assoc-equal section table))
       (table (if self (remove-equal self table) table))
       (table (sdm-instruction-table-organize table))
       (all-catalogued (append (sdm-instruction-table-unimplemented-instructions table)
                                (sdm-instruction-table-implemented-instructions table)))
       (uncatalogued (set::difference (set::mergesort (all-opcode-maps))
                                      (set::mergesort all-catalogued))))
    uncatalogued))




(defconsts *all-uncatalogued-instructions*
  (b* ((section '(5 50))
       (table (table-alist 'sdm-instruction-sect (w state)))
       (self (assoc-equal section table))
       (table (if self (remove-equal self table) table))
       (table (sdm-instruction-table-organize table))
       (all-catalogued (append (sdm-instruction-table-unimplemented-instructions table)
                                (sdm-instruction-table-implemented-instructions table)))
       (uncatalogued (set::difference (set::mergesort (all-opcode-maps))
                                      (set::mergesort all-catalogued))))
    uncatalogued))


(assert-event (equal (set::mergesort (keep-strings (inst-list->mnemonics *all-uncatalogued-instructions*)))
                     '("#UD" "JMPE" "RESERVEDNOP" "far CALL"
                       "far JMP" "near CALL" "near JMP")))
