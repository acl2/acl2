; X86ISA Library


(in-package "X86ISA")

(include-book "inst-listing")


(define find-unimplemented-opcodes-one-opcode ((inst-lst inst-list-p))

  (b* (((when (atom inst-lst)) nil)
       (inst (car inst-lst))
       ((inst inst))
       (rest (find-unimplemented-opcodes-one-opcode (cdr inst-lst))))
    (if inst.fn
        rest
      (cons inst rest))))

(define find-unimplemented-opcodes ((first-opcode 24bits-p)
                                    (num-opcodes natp)
                                    (map-key keywordp)
                                    (wrld plist-worldp))
  :guard (member-equal
          map-key
          '(:one-byte
            :two-byte
            :0F-38-three-byte
            :0F-3A-three-byte
            :vex-0F :vex-0F-38 :vex-0F-3A
            :evex-0F :evex-0F-38 :evex-0F-3A))

  (b* (((when (zp num-opcodes)) nil)
       (rest (if (24bits-p (1+ first-opcode))
                 (find-unimplemented-opcodes
                  (1+ first-opcode) (1- num-opcodes) map-key wrld)
               (er hard? 'find-unimplemented-opcodes
                   "Illegal opcode ~s0.~%" (str::hexify (1+ first-opcode)))))
       (map (select-opcode-map map-key))
       (same-opcode-insts (select-insts map :opcode first-opcode))
       (relevant-insts
        (if (member-equal map-key '(:one-byte
                                    :two-byte
                                    :0F-38-three-byte
                                    :0F-3A-three-byte))
            ;; Because of strict-opcode-p, we know that instructions without
            ;; the following CPUID features have empty opcode.vex and
            ;; opcode.evex fields, which means that they are non-AVX opcodes.
            (remove-insts-with-feat same-opcode-insts
                                    (append (list :avx :avx2 :bmi1 :bmi2)
                                            *avx512-feature-flags*))
          ;; Similarly, we know that instructions with these CPUID features are
          ;; AVX opcodes.
          (keep-insts-with-feat same-opcode-insts
                                (append (list :avx :avx2 :bmi1 :bmi2)
                                        *avx512-feature-flags*))))
       ((when (endp relevant-insts)) rest)
       (first-unimplemented
        (find-unimplemented-opcodes-one-opcode relevant-insts)))
    (append first-unimplemented rest)))

;; (find-unimplemented-opcodes #ux0F_00 256 :vex-0F (w state))

(local (in-theory (disable inst-list-p-of-maps)))

(define find-insts-named ((names symbol-listp)
                          (inst-list inst-list-p))
  :returns (unimp-insts inst-list-p)
  (b* (((when (atom inst-list))
        nil)
       ((inst inst) (car inst-list))
       ((when (member-symbol-name (if (stringp inst.mnemonic)
                                      inst.mnemonic
                                    (symbol-name inst.mnemonic))
                                  names))
        (cons (inst-fix inst)
              (find-insts-named names (cdr inst-list)))))
    (find-insts-named names (cdr inst-list))))

(define keep-implemented-insts ((inst-list inst-list-p))
  :returns (impl-insts inst-list-p)
  (if (atom inst-list)
      nil
    (if (inst->fn (car inst-list))
        (cons (inst-fix (car inst-list))
              (keep-implemented-insts (cdr inst-list)))
      (keep-implemented-insts (cdr inst-list)))))

(define keep-unimplemented-insts ((inst-list inst-list-p))
  :returns (unimpl-insts inst-list-p)
  (if (atom inst-list)
      nil
    (if (inst->fn (car inst-list))
        (keep-unimplemented-insts (cdr inst-list))
      (cons (inst-fix (car inst-list))
            (keep-unimplemented-insts (cdr inst-list))))))




(define section-number-< ((x nat-listp)
                          (y nat-listp))
  (cond ((atom y)    nil)
        ((atom x)    t)
        ((< (car x) (car y)) t)
        ((< (car y) (car x)) nil)
        (t (section-number-< (cdr x) (cdr y)))))


(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/strpos" :dir :system)

(define parse-section-number-aux ((strs string-listp))
  (if (atom strs)
      nil
    (cons (str::strval (car strs))
          (parse-section-number-aux (cdr strs)))))

(define parse-section-number ((str stringp))
  :returns (secnum nat-listp)
  (b* ((lst (parse-section-number-aux (str::strtok str '(#\.)))))
    (if (nat-listp lst)
        lst
      (raise "Bad section number: ~s0" str))))

(define parse-section-heading ((heading stringp))
  :returns (mv (secnum nat-listp)
               (title stringp))
  (b* ((space-idx (str::strpos " " heading))
       ((unless space-idx)
        (mv nil (mbe :logic (if (stringp heading) heading "")
                     :exec heading)))
       (secnum (parse-section-number (subseq heading 0 space-idx)))
       (title (subseq heading (+ 1 space-idx) nil)))
    (mv secnum title)))


(defconst *all-opcode-maps*
  (append *one-byte-opcode-map*
          *two-byte-opcode-map*
          *0f-38-three-byte-opcode-map*
          *0f-3a-three-byte-opcode-map*))

(make-event
 `(define all-opcode-maps ()
    :inline t
    :no-function t
    :returns (insts inst-list-p)
    ',*all-opcode-maps*
    ///
    (in-theory (disable (all-opcode-maps)))))

(define inst-list->mnemonics ((insts inst-list-p))
  :Returns (mnemonics)
  :prepwork ((local (in-theory (disable acl2::member-of-cons member-equal))))
  (if (atom insts)
      nil
    (cons (inst->mnemonic (car insts))
          (inst-list->mnemonics (cdr insts)))))

(define keep-strings (x)
  :returns (strings string-listp)
  (if (atom x)
      nil
    (if (stringp (car x))
        (cons (car x) (keep-strings (cdr x)))
      (keep-strings (cdr x)))))

(make-event
 `(define all-mnemonics ()
    :returns (mnemonics string-listp)
    ',(keep-strings (inst-list->mnemonics (all-opcode-maps)))
    ///
    (in-theory (disable (all-mnemonics)))))

(encapsulate nil
  (local (in-theory (disable inst-list-p acl2::member-of-cons member-equal)))
  (fty::deflist inst-list :elt-type inst :true-listp t))

(fty::deftypes sdm-instruction-table
  (defprod sdm-instruction-table-entry
    ((title stringp)
     (implemented inst-list-p)
     (unimplemented inst-list-p)
     (doc stringp)
     (subsecs sdm-instruction-table))
    :layout :alist
    :measure (+ (* 2 (acl2-count x)) 1))
  (fty::defmap sdm-instruction-table
    :key-type nat-listp
    :val-type sdm-instruction-table-entry
    :true-listp t
    :measure (* 2 (acl2-count x)))
  ///
  (defthm len-of-sdm-instruction-table-fix
    (<= (len (sdm-instruction-table-fix x)) (len x))
    :hints(("Goal" :induct (len x)
            :expand ((sdm-instruction-table-fix x))))
    :rule-classes :linear))

(defconst *def-sdm-instruction-section-verbose* nil)

(define symbol-list->names ((x symbol-listp))
  :returns (names string-listp)
  (if (atom x)
      nil
    (cons (symbol-name (car x))
          (symbol-list->names (cdr x)))))


(defines eval-feature-expr
  (define eval-feature-expr (expr
                             (inst inst-p))
    :measure (acl2-count expr)
    (if (atom expr)
        (and expr
             (or (eq expr t)
                 (and (symbolp expr)
                      (case expr
                        (:vex (opcode->vex (inst->opcode inst)))
                        (:vex-256 (and (opcode->vex (inst->opcode inst))
                                       (member-eq :|256| (opcode->vex (inst->opcode inst)))))
                        (:vex-128 (and (opcode->vex (inst->opcode inst))
                                       (member-eq :|256| (opcode->vex (inst->opcode inst)))))
                        (:evex (opcode->evex (inst->opcode inst)))
                        (:no-vex (b* ((opcode (inst->opcode inst)))
                                   (and (not (opcode->vex opcode))
                                        (not (opcode->evex opcode)))))
                        (:rex-w (eq (opcode->rex (inst->opcode inst)) :w))
                        (t (member-eq expr (opcode->feat (inst->opcode inst))))))
                 (equal expr (inst->mnemonic inst)))
             t)
      (case-match expr
        (('not sub) (not (eval-feature-expr sub inst)))
        ((op . exprlist)
         (if (member-eq op '(and or xor))
             (eval-feature-expr-lst op exprlist inst)
           (raise "bad expr: ~x0~%" expr)))
        (& (raise "bad expr: ~x0~%" expr)))))
  (define eval-feature-expr-lst (op
                                 exprs
                                 (inst inst-p))
    :guard (member-eq op '(and or xor))
    :measure (acl2-count exprs)
    (b* (((when (atom exprs)) (eq op 'and))
         (first (eval-feature-expr (car exprs) inst)))
      (case op
        (and (and first
                  (eval-feature-expr-lst op (cdr exprs) inst)))
        (or (or first
                (eval-feature-expr-lst op (cdr exprs) inst)))
        (t (xor first
                (eval-feature-expr-lst op (cdr exprs) inst)))))))

(define keep-insts-satisfying-feature (expr
                                       (insts inst-list-p))
  :returns (new-insts inst-list-p)
  (b* (((when (atom insts)) nil)
       ((inst inst) (car insts)))
    (if (eval-feature-expr expr inst)
        (cons (inst-fix inst)
              (keep-insts-satisfying-feature expr (cdr insts)))
      (keep-insts-satisfying-feature expr (cdr insts)))))





(define def-sdm-instruction-section-fn ((header stringp)
                                        &key
                                        ((mnemonics symbol-listp) 'nil)
                                        (features 't)
                                        (suppress-not-found 'nil)
                                        ((doc stringp) '""))
  (b* (((mv secnum title) (parse-section-heading header))
       (insts (find-insts-named mnemonics (all-opcode-maps)))
       (insts (if (eq features t)
                  insts
                (keep-insts-satisfying-feature features insts)))
       (unimpl-insts (keep-unimplemented-insts insts))
       (impl-insts (keep-implemented-insts insts))
       (not-found-insts (set-difference-equal (symbol-list->names mnemonics)
                                              (inst-list->mnemonics insts)))
       (- (and not-found-insts
               (not suppress-not-found)
               (raise "Not found: ~x0~%" not-found-insts)))
       (entry (make-sdm-instruction-table-entry
               :title title
               :implemented impl-insts
               :unimplemented unimpl-insts
               :doc doc))
       (- (and *def-sdm-instruction-section-verbose*
               (cw "Entry: ~x0~%" entry))))
    `(table sdm-instruction-sect ',secnum ',entry)))

(defmacro def-sdm-instruction-section (&rest args)
  `(make-event (def-sdm-instruction-section-fn . ,args)))


;; (find-unimplemented-opcodes-named
;;  '(MOV CMOVE CMOVZ CMOVNE CMOVNZ CMOVA CMOVNBE CMOVAE CMOVNB CMOVB CMOVNAE
;;        CMOVBE CMOVNA CMOVG CMOVNLE CMOVGE CMOVNL CMOVL CMOVNGE CMOVLE CMOVNG CMOVC
;;        CMOVNC CMOVO CMOVNO CMOVS CMOVNS CMOVP CMOVPE CMOVNP CMOVPO XCHG BSWAP XADD
;;        CMPXCHG CMPXCHG8B PUSH POP PUSHA PUSHAD POPA POPAD CWD CDQ CBW CWDE MOVSX
;;        MOVZX)
;;  (append *one-byte-opcode-map*
;;          *two-byte-opcode-map*
;;          *0f-38-three-byte-opcode-map*
;;          *0f-3a-three-byte-opcode-map*))



(def-sdm-instruction-section "5.1 GENERAL-PURPOSE INSTRUCTIONS")
(def-sdm-instruction-section "5.1.1 Data Transfer Instructions"
  :mnemonics
  '(MOV
    CMOVE/Z  CMOVNE/NZ  CMOVA/NBE CMOVAE/NB/NC CMOVB/C/NAE
    CMOVBE/NA CMOVNLE/G CMOVNL/GE  CMOVL/NGE CMOVLE/NG 
    CMOVP/PE
    CMOVNP/PO 
    CMOVO CMOVNO CMOVS CMOVNS  XCHG
    BSWAP XADD CMPXCHG CMPXCHG8B PUSH POP PUSHA/PUSHAD POPA/POPAD CWD/CDQ/CQO
    CBW/CWDE/CDQE MOVSX MOVZX)
  :doc "<p>Unimplemented instructions are:</p>
<ul>
<li>POP variants that write to segment registers: these have side effects,
perhaps similar to those of MOV to a segment register</li>
<li>CMPEXCHG8B</li>
<li>BSWAP, several variants which just correspond to the same instruction on
different registers encoded in the low 3 bits of the opcode -- seems straightforward?</li>
</ul>")

(def-sdm-instruction-section "5.1.2 Binary Arithmetic Instructions"
  :mnemonics
  '(ADCX ADOX ADD ADC SUB SBB IMUL MUL IDIV DIV INC DEC NEG)
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
                   LOOPNE/LOOPNZ LOOPE/LOOPZ IRET/D/Q
                   JO JNO JS JNS LOOP RET INT INTO BOUND ENTER LEAVE)
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

(def-sdm-instruction-section "5.2 X87 FPU INSTRUCTIONS")
;;   :mnemonics '(FLD FST FSTP FILD FIST FISTP1 FBLD FBSTP FXCH FCMOVE FCMOVNE
;;                    FCMOVB FCMOVBE FCMOVNB FCMOVNBE FCMOVU FCMOVNU)
;;   )
(def-sdm-instruction-section "5.2.1 X87 FPU Data Transfer Instructions"
  :doc "<p>Decoding isn't implemented for X87 instructions (D8-DF escapes from
one byte opcode map)</p>")
(def-sdm-instruction-section "5.2.2 X87 FPU Basic Arithmetic Instructions"
  :doc "<p>Decoding isn't implemented for X87 instructions (D8-DF escapes from
one byte opcode map)</p>")
(def-sdm-instruction-section "5.2.3 X87 FPU Comparison Instructions"
  :doc "<p>Decoding isn't implemented for X87 instructions (D8-DF escapes from
one byte opcode map)</p>")
(def-sdm-instruction-section "5.2.4 X87 FPU Transcendental Instructions"
  :doc "<p>Decoding isn't implemented for X87 instructions (D8-DF escapes from
one byte opcode map)</p>")
(def-sdm-instruction-section "5.2.5 X87 FPU Load Constants Instructions"
  :doc "<p>Decoding isn't implemented for X87 instructions (D8-DF escapes from
one byte opcode map)</p>")
(def-sdm-instruction-section "5.2.6 X87 FPU Control Instructions"
  :doc "<p>Decoding isn't implemented for X87 instructions (D8-DF escapes from
one byte opcode map).</p>

<p>Note also a few of X86 control instructions can be encoded using 0x9B as a
prefix -- currently this is decoded as a one-byte no-op (FWAIT/WAIT), which I
think must be wrong.</p>")

(def-sdm-instruction-section "5.3 X87 FPU AND SIMD STATE MANAGEMENT INSTRUCTIONS"
  :mnemonics '(FXSAVE FXRSTOR))

(def-sdm-instruction-section "5.4 MMX INSTRUCTIONS")
(def-sdm-instruction-section "5.4.1 MMX Data Transfer Instructions"
  :mnemonics '(MOVD/Q)
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
  implemented.</p>

<p>Possible bug: Two-byte opcode PMULHW (0x0FE5) is listed with feature :SSE
but manual lists feature MMX</p>")

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

(def-sdm-instruction-section "5.5 INTEL(R) SSE INSTRUCTIONS")
(def-sdm-instruction-section "5.5.1 Intel(R) SSE SIMD Single Precision Floating-Point Instructions")
(def-sdm-instruction-section "5.5.1.1 Intel(R) SSE Data Transfer Instructions"
  :mnemonics '(MOVAPS MOVUPS MOVHPS MOVHLPS MOVLPS MOVLHPS MOVMSKPS MOVSS)
  ;; :features :sse
  :doc "<p>Unimplemented:</p>
<ul>
<li>MOVHLPS</li>
<li>MOVLHPS</li>
<li>MOVMSKPS</li>
</ul>
<p>Note: We have versions of MOVLPS, MOVHPS, MOVHLPS, MOVLHPS that do not
have :SSE among the features -- may be a bug</p>")

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
  ;; :features :sse
  :doc "<p>Seems strange that CVTPI2PS, CVTPS2PI, CVTTPS2PI don't require SSE
  feature, but they don't list that requirement in the SDM either</p>")

(def-sdm-instruction-section "5.5.2 Intel(R) SSE MXCSR State Management Instructions"
  :mnemonics '(LDMXCSR STMXCSR)
  ;; :features :sse
  :doc "<p>Possible bug: these don't require the SSE feature</p>")

(def-sdm-instruction-section "5.5.3 Intel(R) SSE 64-Bit SIMD Integer Instructions"
  :mnemonics '(PAVGB PAVGW PEXTRW PINSRW PMAXUB PMAXSW PMINUB PMINSW PMOVMSKB PMULHUW PSADBW PSHUFW)
  :features '(not (or :sse2 (and (not "PSHUFW") :mmx) :avx))
  :doc "<p>None of these are implemented.</p>
<p>Possible bugs:</p>
<ul>
<li>PINSRW and some PEXTRW instructions don't list SSE/SSE2 features</li>
<li>PSHUFW lists MMX as feature, but it's not listed in SDM and is part of SSE extensions even though it operates on an MM register</li>
</ul>")

(def-sdm-instruction-section "5.5.4 Intel(R) SSE Cacheability Control, Prefetch, and Instruction Ordering Instructions"
  :mnemonics '(;; PREFETCHIT0 PREFETCHIT1
               MASKMOVQ MOVNTQ MOVNTPS PREFETCHT0 PREFETCHT1 PREFETCHT2 PREFETCHNTA SFENCE)
  :doc "<p>Unimplemented: MOVNTPS, SFENCE, MOVNTQ, MASKMOVQ.</p>
<p>Implemented instructions (PREFETCHNTA, PREFETCHT0, PREFETCHT1, PREFETCHT2) are no-ops.</p>
<p>Possible bugs:</p>
<ul>
<li>PREFETCHIT1 and PREFETCHIT2 are missing.</li>
<li>MOVNTQ and MASKMOVQ list MMX features, but don't list them in the SDM (and these are part of the SSE extension even though they operate on MM registers).</li>
<li>SFENCE lists SSE feature which (perhaps oddly) isn't present in SDM</li>
</ul>")

(def-sdm-instruction-section "5.6 INTEL(R) SSE2 INSTRUCTIONS")
(def-sdm-instruction-section "5.6.1 Intel(R) SSE2 Packed and Scalar Double Precision Floating-Point Instructions")
(def-sdm-instruction-section "5.6.1.1 Intel(R) SSE2 Data Movement Instructions"
  :mnemonics '(MOVAPD MOVUPD MOVHPD MOVLPD MOVMSKPD)
  :features :sse2
  :doc "<p>Unimplemented: MOVMSKPD</p>")
(def-sdm-instruction-section "5.6.1.2 Intel(R) SSE2 Packed Arithmetic Instructions"
  :mnemonics '(ADDPD ADDSD SUBPD SUBSD MULPD MULSD DIVPD DIVSD SQRTPD SQRTSD MAXPD MINPD MINSD)
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
float-integer are implemented as are scalar and packed float-float.</p>
<p>Possible bugs: CVTPI2PD, CVTTPD2PI, CVTPD2PI list :MMX feature rather than :SSE2.</p>")

(def-sdm-instruction-section "5.6.2 Intel(R) SSE2 Packed Single Precision Floating-Point Instructions"
  :mnemonics '(CVTDQ2PS CVTPS2DQ CVTTPS2DQ)
  :features :sse2
  :doc "<p>Unimplemented</p>")

(def-sdm-instruction-section "5.6.3 Intel(R) SSE2 128-Bit SIMD Integer Instructions"
  :mnemonics '(MOVDQA MOVDQU MOVQ2DQ MOVDQ2Q PMULUDQ PADDQ PSUBQ
                      PSHUFLW PSHUFHW PSHUFD PSLLDQ PSRLDQ PUNPCKHQDQ PUNPCKLQDQ)
  :features '(or :sse2 "PSLLDQ" "PSRLDQ" "PSUBQ" "PMULUDQ" "PADDQ")
  :doc "<p>Unimplemented:</p>
<ul>
<li>PUNPCKLQDQ, PUNPCKHQDQ</li>
<li>PSHUFD, PSHUFHW PSHUFLW</li>
<li>MOVDQ2DQ, MOVDQ2Q</li>
<li>PADDQ, PSUBQ (MM register versions)</li>
<li>PMULUDQ</li>
</ul>

<p>Possible bugs</p>
<ul>
<li>PSLLDQ, PSRLDQ missing SSE2 feature</li>
<li>PSUBQ and PMULUDQ (mm register versions) lists MMX feature rather than SSE2
as in SDM -- unlike PADDQ which has an MMX version in SDM, but isn't listed
among the MMX arithmetic instructions (@(see |5.4.3 MMX Packed Arithmetic Instructions|)).
 (Is SDM correct on these?)</li>
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

(def-sdm-instruction-section "5.7 INTEL(R) SSE3 INSTRUCTIONS")
(def-sdm-instruction-section "5.7.1 Intel(R) SSE3 x87-FP Integer Conversion Instruction"
  :doc "<p>Like other x87 instructions, FISTTP is not listed in opcode maps</p>")

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

(def-sdm-instruction-section "5.8 SUPPLEMENTAL STREAMING SIMD EXTENSIONS 3 (SSSE3) INSTRUCTIONS")
(def-sdm-instruction-section "5.8.1 Horizontal Addition/Subtraction"
  :mnemonics '(PHADDW PHADDSW PHADDD PHSUBW PHSUBSW PHSUBD)
  :features '(or :ssse3 "PHADDW")
  :doc "<p>Possible bug: one version of PHADDW has SSE3 feature instead of SSSE3</p>")

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

(def-sdm-instruction-section "5.9 INTEL(R) SSE4 INSTRUCTIONS")
(def-sdm-instruction-section "5.10 INTEL(R) SSE4.1 INSTRUCTIONS")
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
  :features '(or :sse4.1 "PMINUW")
  :doc "<p>Possible bug: PMINUW listed with SSE2 rather than SSE4.1 feature</p>")
(def-sdm-instruction-section "5.10.6 Floating-Point Round Instructions with Selectable Rounding Mode"
  :mnemonics '(ROUNDPS ROUNDPD ROUNDSS ROUNDSD)
  :features :sse4.1)
(def-sdm-instruction-section "5.10.7 Insertion and Extractions from XMM Registers"
  :mnemonics '(EXTRACTPS INSERTPS PINSRB PINSRD/Q PEXTRB PEXTRW PEXTRD/Q)
  ;; :features :sse4.1
  :doc "<p>Possible bugs: PEXTRB and PEXTRW (0x66_0F_3A_15) missing SSE4.1 feature</p>")

(def-sdm-instruction-section "5.10.8 Packed Integer Format Conversions"
  :mnemonics '(PMOVSXBW PMOVZXBW PMOVSXBD PMOVZXBD PMOVSXWD PMOVZXWD
                        PMOVSXBQ PMOVZXBQ PMOVSXWQ PMOVZXWQ PMOVSXDQ PMOVZXDQ)
  ;; :features '(not :avx2)
  :doc "<p>Features are missing for these</p>")

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

(def-sdm-instruction-section "5.11 INTEL(R) SSE4.2 INSTRUCTION SET")
(def-sdm-instruction-section "5.11.1 String and Text Processing Instructions"
  :mnemonics '(PCMPESTRI PCMPESTRM PCMPISTRI PCMPISTRM)
  :features :sse4.2)
(def-sdm-instruction-section "5.11.2 Packed Comparison SIMD Integer Instruction"
  :mnemonics '(PCMPGTQ)
  :features :sse4.2)
(def-sdm-instruction-section "5.12 INTEL(R) AES-NI AND PCLMULQDQ"
  :mnemonics '(AESDEC AESDECLAST AESENC AESENCAST AESIMC AESKEYGENASSIST PCLMULQDQ)
  :doc "<p>AESENCLAST is misspelled AESENCAST</p>")

(def-sdm-instruction-section "5.13 INTEL(R) ADVANCED VECTOR EXTENSIONS (INTEL(R) AVX)"
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
               VAESIMC AESKEYGENASSIST
               )
  :features '(and (or :avx "VPMOVZXDQ") :vex)
  :doc "<p>Possible bugs:</p>
<ul>
<li>VEX version of AESKEYGENASSIST should be called VAESKEYGENASSIST</li>
<li>AVX/VEX.128 version of VPMOVZXDQ is missing from opcode map (but we have AVX2/VEX.256 version)</li>
</ul>
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
               ;;BOZO
               movsd)
  :features '(and :avx :vex)
  :doc "<p>Probable bug: VMOVSD (opcode VEX.LIG.F2.0F.WIG 10) is listed with mnemonic MOVSD</p>")


(def-sdm-instruction-section "5.14 16-BIT FLOATING-POINT CONVERSION"
  :mnemonics '(VCVTPH2PS VCVTPS2PH)
  :features :vex)

(def-sdm-instruction-section "5.15 FUSED-MULTIPLY-ADD (FMA)"
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

(def-sdm-instruction-section "5.16 INTEL(R) ADVANCED VECTOR EXTENSIONS 2 (INTEL(R) AVX2)"
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
 VPMULDQ VPMULLD VPCMPGTQ)
  :features '(and :vex-256 (or :avx2 "VPMINUB" "VPMAXUB" "VPMINSW"))
  :doc "<p>Possible bugs: VPMINUB, VPMAXUB, VPMINSW (vex-256 versions) have feature AVX rather than AVX2</p>")

(def-sdm-instruction-section "5.16.14.19 Promoted Vector Integer SIMD Instructions in Intel(R) AVX2"
  :mnemonics '(VBROADCASTI128 VBROADCASTSD VBROADCASTSS VEXTRACTI128
 VINSERTI128 VPMASKMOVD VPMASKMOVQ VPERM2I128 VPERMD VPERMPS VPERMQ VPERMPD
 VPBLENDD VPSLLVD VPSLLVQ VPSRAVD VPSRLVD VPSRLVQ VGATHERDPD VGATHERQPD
 VGATHERDPS VGATHERQPS VPGATHERDD VPGATHERQD VPGATHERDQ VPGATHERQQ)
  :features :avx2)


(def-sdm-instruction-section "5.17 INTEL(R) TRANSACTIONAL SYNCHRONIZATION EXTENSIONS (INTEL(R) TSX)"
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

(def-sdm-instruction-section "5.18 INTEL(R) SHA EXTENSIONS"
  :mnemonics '(SHA1MSG1 SHA1MSG2 SHA1NEXTE SHA1RNDS4 SHA256MSG1 SHA256MSG2 SHA256RNDS2))

(def-sdm-instruction-section "5.19 INTEL(R) ADVANCED VECTOR EXTENSIONS 512 (INTEL(R) AVX-512)"
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
               VCVTQQ2PD VCVTQQ2PS
               VCVTTSD2USI VCVTSD2USI
               VCVTTSS2USI VCVTSS2USI
               VCVTUDQ2PD VCVTUDQ2PS
               VCVTUSI2SD VCVTUSI2SS
               VEXPANDPD VEXPANDPS
               VEXTRACTF32X4 ;; VEXTRACTF64X4
               VEXTRACTI32X4 ;; VEXTRACTI64X4
               VFIXUPIMMPD VFIXUPIMMPS
               VFIXUPIMMSD VFIXUPIMMSS
               VGETEXPPD VGETEXPPS
               VGETEXPSD VGETEXPSS
               VGETMANTPD VGETMANTPS
               VGETMANTSD VGETMANTSS
               VINSERTF32X4 ;; VINSERTF64X4
               VMOVDQA32 VMOVDQA64
               VMOVDQU32 VMOVDQU64
               VPBLENDMD VPBLENDMQ
               VPBROADCASTD VPBROADCASTQ
               VPCMPD ;; VPCMPUD
               VPCMPQ ;; VPCMPUQ
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
               VPMOVSQB VPMOVUSQB
               VPMOVSQW VPMOVUSQW
               VPMOVSQD VPMOVUSQD
               VPMOVSDB VPMOVUSDB
               VPMOVSDW VPMOVUSDW
               VPROLD ;; VPROLQ
               VPROLVD VPROLVQ
               VPRORD ;; VPRORQ
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
               VPSCATTERDD VPSCATTERDQ
               VPSCATTERQD VPSCATTERQQ
               VSHUFF32X4 VSHUFF64X2
               VSHUFI32X4 VSHUFI64X2
               )
  :doc "<p>Possible bugs:</p>
<ul>
<li>VEXTRACTF32x8 and VEXTRACTF64x4 (both 0x0F_3A_1B) are listed with mnemonics VEXTRACTF32x4 and VEXTRACTF64x2</li>
<li>similar for VEXTRACTI*, VINSERTF*</li>
<li>VPCMPUD and VPCMPUQ (both 0x0F_3A_1E) are listed with mnemonics VPCMPD and VPCMPQ</li>
<li>VPROLQ (0x0F72 evex.W1) is listed with mnemonic VPROLD</li>
</ul>"
  )

(def-sdm-instruction-section "5.19.2 AVX-512BW instructions that are not Intel AVX or AVX2 promotions"
  :mnemonics '(VDBPSADBW
               VMOVDQU8 VMOVDQU16
               VPBLENDMB
               VPBLENDMW
               VPBROADCASTB VPBROADCASTW
               VPCMPB ;;VPCMPUB
               VPCMPW ;;VPCMPUW
               VPERMW
               VPERMI2B VPERMI2W
               VPMOVM2B VPMOVM2W
               VPMOVB2M VPMOVW2M
               VPMOVSWB VPMOVUSWB
               VPSLLVW VPSRAVW VPSRLVW
               VPTESTNMB VPTESTNMW
               VPTESTMB VPTESTMW)
  :doc "<p>Possible bugs: VPCMPUB and VPCMPUW (both 0x0F_3A_3E) are listed with mnemonics VPCMPB and VPCMPW</p>")

(def-sdm-instruction-section "5.19.3  AVX-512CD instructions that are not Intel AVX or AVX2 promotions"
  :mnemonics '(VPBROADCASTMB2Q VPBROADCASTMW2D
               VPCONFLICTD VPCONFLICTQ
               VPLZCNTD VPLZCNTQ))

(def-sdm-instruction-section "5.19.4 Opmask instructions"
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

(def-sdm-instruction-section "5.19.5 AVX-512ER instructions"
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

(def-sdm-instruction-section "5.19.6 AVX-512PF instructions"
  :mnemonics '(VGATHERPF0DPD VGATHERPF0DPS VGATHERPF0QPD VGATHERPF0QPS
                             VGATHERPF1DPD VGATHERPF1DPS VGATHERPF1QPD VGATHERPF1QPS VSCATTERPF0DPD
                             VSCATTERPF0DPS VSCATTERPF0QPD VSCATTERPF0QPS VSCATTERPF1DPD VSCATTERPF1DPS
                             VSCATTERPF1QPD VSCATTERPF1QPS))

(def-sdm-instruction-section "5.19.7 AVX512-FP16 instructions"
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


(def-sdm-instruction-section "5.20 SYSTEM INSTRUCTIONS"
  :mnemonics '(CLAC STAC LGDT SGDT LLDT SLDT LTR STR LIDT SIDT ;; MOV
                    LMSW CLTS ARPL LAR LSL VERR VERW           ;; MOV
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


(def-sdm-instruction-section "5.21 64-BIT MODE INSTRUCTIONS"
  :mnemonics '(CBW/CWDE/CDQE CMPS/W/D CMPXCHG16B LODS/W/D/Q MOVS/W/D/Q MOVZX
                             STOS/W/D/Q SWAPGS SYSCALL SYSRET)
  :doc "
<ul>
<li>Perhaps CMPS/W/D should be called CMPS/W/D/Q</li>
</ul>")

(def-sdm-instruction-section "5.22 VIRTUAL-MACHINE EXTENSIONS"
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

(def-sdm-instruction-section "5.23 SAFER MODE EXTENSIONS"
  :mnemonics '(GETSEC))
(def-sdm-instruction-section "5.24 INTEL(R) MEMORY PROTECTION EXTENSIONS"
  :mnemonics '(BNDMK BNDCL BNDCU BNDCN BNDMOV BNDMOV BNDLDX BNDSTX))

(def-sdm-instruction-section "5.25 INTEL(R) SOFTWARE GUARD EXTENSIONS"
  :mnemonics '(ENCLS ENCLU))
(def-sdm-instruction-section "5.26 SHADOW STACK MANAGEMENT INSTRUCTIONS"
  :mnemonics nil 
  ;; '(CLRSSBSY INCSSP RDSSP RSTORSSP SAVEPREVSSP SETSSBSY WRSS WRUSS)
  :doc "<p>Not yet included in opcode maps</p>")

(def-sdm-instruction-section "5.27 CONTROL TRANSFER TERMINATING INSTRUCTIONS"
  :mnemonics nil  ;; '(ENDBR32 ENDBR64 )
  :doc "<p>Not yet included in opcode maps</p>")
(def-sdm-instruction-section "5.28 INTEL(R) AMX INSTRUCTIONS"
  :mnemonics nil
  ;; '(LDTILECFG STTILECFG TDPBF16PS TDPBSSD TDPBSUD TDPBUSD TDPBUUD
  ;;                        TILELOADD TILELOADDT1 TILERELEASE TILESTORED TILEZERO)
  :doc "<p>Not yet included in opcode maps</p>")
(def-sdm-instruction-section "5.29 USER INTERRUPT INSTRUCTIONS"
  :mnemonics nil
  ;; '(CLUI SENDUIPI STUI TESTUI UIRET)
  :doc "<p>Not yet included in opcode maps</p>")
(def-sdm-instruction-section "5.30 ENQUEUE STORE INSTRUCTIONS"
  :mnemonics nil
  ;; '(ENQCMD ENQCMDS)
  :doc "<p>Not yet included in opcode maps</p>")
(def-sdm-instruction-section "5.31 INTEL(R) ADVANCED VECTOR EXTENSIONS 10 VERSION 1 INSTRUCTIONS")




(define sdm-instruction-pair-p (x)
  (and (consp x)
       (nat-listp (car x))
       (sdm-instruction-table-entry-p (cdr x)))
  ///
  (defthm sdm-instruction-pair-p-when-reqs
    (implies (and (nat-listp (car x))
                  (sdm-instruction-table-entry-p (cdr x)))
             (sdm-instruction-pair-p x))))

(define sdm-instruction-pair-< ((x sdm-instruction-pair-p)
                                (y sdm-instruction-pair-p))
  :prepwork ((local (in-theory (enable sdm-instruction-pair-p))))
  (section-number-< (car X) (car y)))

(encapsulate nil
  (local (in-theory (enable sdm-instruction-pair-<
                            sdm-instruction-pair-p
                            section-number-<)))

  (local (defthm section-number-<-transitive
           (implies (and (section-number-< x y)
                         (section-number-< y z))
                    (section-number-< x z))))

  (local (defthm section-number->=-transitive
           (implies (and (not (section-number-< x y))
                         (not (section-number-< y z)))
                    (not (section-number-< x z)))))

  (local (defthm section-number-<-irreflexive
           (not (section-number-< x x))))

  (local (in-theory (disable section-number-<)))

  (acl2::defsort sdm-instruction-table-sort
    :prefix sdm-instruction-table
    ;; :comparable-listp sdm-instruction-table-p
    :compare< sdm-instruction-pair-<
    :comparablep sdm-instruction-pair-p
    :true-listp t)

  (defthm sdm-instruction-table-list-p-is-sdm-instruction-table-p
    (equal (sdm-instruction-table-list-p x)
           (sdm-instruction-table-p x))
    :hints(("Goal" :in-theory (enable sdm-instruction-table-p
                                      sdm-instruction-table-list-p))))

  (defthm sdm-instruction-table-p-of-insertsort
    (implies (sdm-instruction-table-p x)
             (sdm-instruction-table-p (sdm-instruction-table-insertsort x)))
    :hints (("goal" :use sdm-instruction-table-insertsort-creates-comparable-listp
             :in-theory (disable sdm-instruction-table-insertsort-creates-comparable-listp)))))



(define sdm-instruction-table-gather-subtopics ((prefix nat-listp)
                                        (x sdm-instruction-table-p))
  :returns (mv (prefixed-x sdm-instruction-table-p)
               (rest-x sdm-instruction-table-p))
  :measure (len x)
  :verify-guards nil
  (b* (((when (atom x)) (mv nil nil))
       ((unless (mbt (and (consp (car x))
                          (nat-listp (caar x)))))
        (sdm-instruction-table-gather-subtopics prefix (cdr x)))
       (x1-section (caar x))
       ((unless (acl2::prefixp (acl2::nat-list-fix prefix) x1-section))
        (mv nil (sdm-instruction-table-fix x)))
       ;; first element is still prefixed by the input prefix, continue with the rest
       ;; first gather all the elements that are prefixed by section:
       ((mv x1-subsecs rest-x) (sdm-instruction-table-gather-subtopics x1-section (cdr x)))
       ((sdm-instruction-table-entry entry) (cdar x))
       (new-x1 (cons x1-section (change-sdm-instruction-table-entry entry :subsecs (append entry.subsecs x1-subsecs))))
       ((unless (mbt (< (len rest-x) (len x))))
        (mv (list new-x1) rest-x))
       ((mv rest rest-x) (sdm-instruction-table-gather-subtopics prefix rest-x)))
    (mv (cons new-x1 rest) rest-x))
  ///
  (defret <fn>-rest-x-length
    (<= (len rest-x) (len x))
    :rule-classes :linear)

  (verify-guards sdm-instruction-table-gather-subtopics))

(define sdm-instruction-table-organize ((x sdm-instruction-table-p))
  ;; top level: sort, then gather subtopics
  :returns (organized sdm-instruction-table-p)
  (b* ((sorted (sdm-instruction-table-sort x))
       ((mv gathered &) (sdm-instruction-table-gather-subtopics nil sorted)))
    gathered))

(defines sdm-instruction-table-elide
  ;; this is just so we can look at the hierarchy of topics without seeing everything
  (define sdm-instruction-table-elide ((x sdm-instruction-table-p))
    :measure (sdm-instruction-table-count x)
    :returns (new-x sdm-instruction-table-p)
    :verify-guards nil
    (b* ((x (sdm-instruction-table-fix x)))
      (if (atom x)
          nil
        (cons (cons (caar x) (sdm-instruction-table-entry-elide (cdar x)))
              (sdm-instruction-table-elide (cdr x))))))
  (define sdm-instruction-table-entry-elide ((x sdm-instruction-table-entry-p))
    :measure (sdm-instruction-table-entry-count x)
    :returns (new-x sdm-instruction-table-entry-p)
    (b* (((sdm-instruction-table-entry x)))
      (change-sdm-instruction-table-entry x :subsecs (sdm-instruction-table-elide x.subsecs)
                                          :implemented nil :unimplemented nil :doc "")))
  ///
  (verify-guards sdm-instruction-table-elide))

(define section-number-string-aux ((x nat-listp)
                                   (acc str::printtree-p))
  :returns (str stringp :rule-classes :type-prescription)
  (if (atom x)
      (str::printtree->str acc)
    (section-number-string-aux (cdr x)
                               (str::pcat acc (str::natstr (car x))
                                          (if (consp (cdr x)) "." "")))))

(define section-number-string ((x nat-listp))
  (section-number-string-aux x nil))

(define sdm-instruction-table-entry-topicname ((section nat-listp)
                                               (x sdm-instruction-table-entry-p))
  (intern-in-package-of-symbol (str::cat (section-number-string section) " "
                                         (sdm-instruction-table-entry->title x))
                               'x86isa-package))

(define sdm-instruction-table-instruction-counts ((x sdm-instruction-table-p))
  :measure (sdm-instruction-table-count x)
  :returns (mv (impl-count natp :rule-classes :type-prescription)
               (unimpl-count natp :rule-classes :type-prescription))
  :verify-guards nil
  (b* ((x (sdm-instruction-table-fix x))
       ((when (atom x)) (mv 0 0))
       ((sdm-instruction-table-entry entry) (cdar x))
       ((mv sub-impl sub-unimpl) (sdm-instruction-table-instruction-counts entry.subsecs))
       ((mv rest-impl rest-unimpl) (sdm-instruction-table-instruction-counts (cdr x))))
    (mv (+ (len entry.implemented) sub-impl rest-impl)
        (+ (len entry.unimplemented) sub-unimpl rest-unimpl)))
  ///
  (verify-guards sdm-instruction-table-instruction-counts))

(define create-sdm-subsec-summary-aux ((x sdm-instruction-table-p)
                                       (acc str::printtree-p))
  :returns (new-acc str::printtree-p)
  (b* (((when (atom x))
        (str::printtree-fix acc))
       ((unless (mbt (and (consp (car x)) (nat-listp (caar x)))))
        (create-sdm-subsec-summary-aux (cdr x) acc))
       ((cons section (sdm-instruction-table-entry entry)) (car x))
       (acc (str::pcat acc "<tr><td>@(see |" (symbol-name (sdm-instruction-table-entry-topicname section entry)) "|)</td>"))
       ((mv sub-impl sub-unimpl) (sdm-instruction-table-instruction-counts entry.subsecs))
       (impl (+ (len entry.implemented) sub-impl))
       (unimpl (+ (len entry.unimplemented) sub-unimpl))
       (acc (str::pcat acc "<td>" (str::natstr impl) "</td>"))
       (acc (str::pcat acc "<td>" (str::natstr unimpl) "</td>"))
       (acc (str::pcat acc "<td>" (str::natstr (+ impl unimpl)) "</td></tr>" #\Newline)))
    (create-sdm-subsec-summary-aux (cdr x) acc)))
           

(define create-sdm-subsec-summary ((x sdm-instruction-table-p))
  (b* ((acc nil)
       (acc (str::pcat acc
                       "<table> <th>Subsection</th> <th>Implemented</th> <th>Unimplemented</th> <th>Total</th>"
                       #\Newline))
       (acc (create-sdm-subsec-summary-aux x acc))
       (acc (str::pcat acc "</table>" #\Newline)))
    (str::printtree->str acc)))
  

(define sdm-instruction-entry-xdoc ((topicname symbolp)
                                    (x sdm-instruction-table-entry-p)
                                    (parent symbolp))
  (b* (((sdm-instruction-table-entry x))
       ((mv sub-impl sub-unimpl) (sdm-instruction-table-instruction-counts x.subsecs)))
    `((defxdoc ,topicname
        :parents (,parent)
        :long ,(str::cat x.doc acl2::*newline-string*
                         (if x.unimplemented
                             (str::cat "<h3>Unimplemented Instructions</h3>" acl2::*newline-string*
                                       (create-insts-doc x.unimplemented :full-opcode? t)
                                       acl2::*newline-string*)
                           "")
                         (if x.implemented
                             (str::cat
                              "<h3>Implemented Instructions</h3>" acl2::*newline-string*
                              (create-insts-doc x.implemented :full-opcode? t)
                              acl2::*newline-string*)
                           "")
                         (if x.subsecs
                             (str::cat "<h3>Subsections</h3>"
                                       "<p>Total instructions: " (str::natstr (+ sub-impl sub-unimpl))
                                       ", Implemented: " (str::natstr sub-impl)
                                       ", Unimplemented: " (str::natstr sub-unimpl)
                                       "</p>" acl2::*newline-string*
                                       (create-sdm-subsec-summary x.subsecs))
                           "")))
      ;; Order subtopics in the order defined
      (xdoc::order-subtopics ,topicname nil t))))

(define sdm-instruction-table-xdoc-events ((x sdm-instruction-table-p)
                                           (parent symbolp))
  ;; Run on organized instruction table
  :measure (sdm-instruction-table-count x)
  (b* ((x (sdm-instruction-table-fix x))
       ((when (atom x)) nil)
       ((cons section (sdm-instruction-table-entry entry)) (car x))
       (topicname (sdm-instruction-table-entry-topicname section entry))
       (doc1 (sdm-instruction-entry-xdoc topicname entry parent))
       (subsec-docs (sdm-instruction-table-xdoc-events entry.subsecs topicname)))
    (append doc1 subsec-docs (sdm-instruction-table-xdoc-events (cdr x) parent))))




(defxdoc  sdm-instruction-set-summary
  :parents (x86isa)
  :short "Summary of what instructions are implemented/unimplemented, as organized in the
Instruction Set Summary of the Intel Software Developer Manual (volume 1
chapter 5)."
  :long (b* ((subsecs
              (sdm-instruction-table-organize
               (table-alist 'sdm-instruction-sect (w state))))
             ((mv sub-impl sub-unimpl)
              (sdm-instruction-table-instruction-counts subsecs)))
          (str::cat
           "<p>Note: this summary is based on the opcode maps (see @(see implemented-instructions) and subtopics).
To the extent that the opcode maps are incomplete (as noted in several of the
below topics), the instruction counts listed below and in subtopics are as
well.</p>"

           "<h3>Subsections</h3>"
                  "<p>Total instructions: " (str::natstr (+ sub-impl sub-unimpl))
                  ", Implemented: " (str::natstr sub-impl)
                  ", Unimplemented: " (str::natstr sub-unimpl)
                  "</p>" acl2::*newline-string*
                  (create-sdm-subsec-summary subsecs))))


(with-output :off (event)
  (make-event
   (b* ((table (table-alist 'sdm-instruction-sect (w state))))
     (cons 'progn (sdm-instruction-table-xdoc-events
                   (sdm-instruction-table-organize table)
                   'sdm-instruction-set-summary)))))

#|
(include-book
"xdoc/save" :dir :system)

(xdoc::save "catalogue-manual" :redef-okp t)
|#
