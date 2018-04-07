(IN-PACKAGE "ACL2")

(VALUE-TRIPLE
     '(:GENERATED-BY (L3-TO-ACL2 "mips-acl2.txt" "mips.lisp"
                                 :STR-TO-SYM '(("LOAD" . IS_LOAD)
                                               ("STORE" . IS_STORE)
                                               ("INSTRUCTION" . IS_INSTRUCTION)
                                               ("DATA" . IS_DATA)
                                               ("gpr" . GPREGS)))))

(INCLUDE-BOOK "projects/translators/l3-to-acl2/translator/l3"
              :DIR :SYSTEM)

(VALUE-TRIPLE (LIST :ERROR (VAL _ = RECORD
                                ("StatusRegister" (SQBKT ("'rst" (FTY 23))
                                                         ("BEV" BTY)
                                                         ("ERL" BTY)
                                                         ("EXL" BTY)
                                                         ("IE" BTY)
                                                         ("IM0" BTY)
                                                         ("IM1" BTY)
                                                         ("KSU" (FTY 2))
                                                         ("RE" BTY))))))

(VALUE-TRIPLE
    (LIST :ERROR (VAL _ = RECORD
                      ("ConfigRegister" (SQBKT ("'rst" (FTY 31)) ("BE" BTY))))))

(VALUE-TRIPLE (LIST :ERROR (VAL _ = RECORD
                                ("CauseRegister" (SQBKT ("'rst" (FTY 27))
                                                        ("ExcCode" (FTY 5)))))))

(VALUE-TRIPLE
     (LIST :ERROR (VAL _ = RECORD
                       ("CP0" (SQBKT ("Cause" (CTY "CauseRegister"))
                                     ("Config" (CTY "ConfigRegister"))
                                     ("Count" F32)
                                     ("EPC" F64)
                                     ("ErrorEPC" F64)
                                     ("Status" (CTY "StatusRegister")))))))

(CONSTRUCT HLSTATUS (HLARITH HLOK HLMTHI HLMTLO))

(CONSTRUCT IORD (IS_INSTRUCTION IS_DATA))

(CONSTRUCT LORS (IS_LOAD IS_STORE))

(CONSTRUCT EXCEPTIONTYPE
           (ADEL ADES SYS BP RI OV TR))

(CONSTRUCT BRANCH
           ((BEQ ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (BEQL ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))
            (BGEZ ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BGEZAL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BGEZALL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BGEZL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BGTZ ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BGTZL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BLEZ ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BLEZL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BLTZ ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BLTZAL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BLTZALL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BLTZL ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (BNE ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (BNEL ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))
            (J (UNSIGNED-BYTE 26))
            (JAL (UNSIGNED-BYTE 26))
            (JALR ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (JR (UNSIGNED-BYTE 5))))

(CONSTRUCT CP
           ((DMFC0 ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 3)))
            (DMTC0 ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 3)))
            (MFC0 ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 3)))
            (MTC0 ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 3)))))

(CONSTRUCT STORE
           ((SB ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (SC ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (SCD ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (SD ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (SDL ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (SDR ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (SH ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (SW ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (SWL ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (SWR ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))))

(CONSTRUCT LOAD
           ((LB ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (LBU ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LD ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (LDL ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LDR ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LH ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (LHU ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LL ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (LLD ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LW ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 16)))
            (LWL ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LWR ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (LWU ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))))

(CONSTRUCT TRAP
           ((TEQ ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (TEQI ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (TGE ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (TGEI ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (TGEIU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (TGEU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (TLT ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (TLTI ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (TLTIU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (TLTU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (TNE ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (TNEI ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))))

(CONSTRUCT SHIFT
           ((DSLL ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (DSLL32 ((UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)))
            (DSLLV ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)))
            (DSRA ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (DSRA32 ((UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)))
            (DSRAV ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)))
            (DSRL ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (DSRL32 ((UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)))
            (DSRLV ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)))
            (SLL ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (SLLV ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (SRA ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (SRAV ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (SRL ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (SRLV ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))))

(CONSTRUCT MULTDIV
           ((DDIV ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (DDIVU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (DIV ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (DIVU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (DMULT ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (DMULTU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (MFHI (UNSIGNED-BYTE 5))
            (MFLO (UNSIGNED-BYTE 5))
            (MTHI (UNSIGNED-BYTE 5))
            (MTLO (UNSIGNED-BYTE 5))
            (MULT ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))
            (MULTU ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 5)))))

(CONSTRUCT ARITHR
           ((ADD ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (ADDU ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (AND ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (DADD ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (DADDU ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)))
            (DSUB ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (DSUBU ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)))
            (NOR ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (OR ((UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)
                 (UNSIGNED-BYTE 5)))
            (SLT ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (SLTU ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (SUB ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))
            (SUBU ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)))
            (XOR ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)))))

(CONSTRUCT ARITHI
           ((ADDI ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))
            (ADDIU ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 16)))
            (ANDI ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))
            (DADDI ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 16)))
            (DADDIU ((UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 5)
                     (UNSIGNED-BYTE 16)))
            (LUI ((UNSIGNED-BYTE 5) (UNSIGNED-BYTE 16)))
            (ORI ((UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 5)
                  (UNSIGNED-BYTE 16)))
            (SLTI ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))
            (SLTIU ((UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 5)
                    (UNSIGNED-BYTE 16)))
            (XORI ((UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 5)
                   (UNSIGNED-BYTE 16)))))

(CONSTRUCT INSTRUCTION
           ((ARITHI ARITHI)
            (ARITHR ARITHR)
            BREAK (BRANCH BRANCH)
            (CP CP)
            ERET (LOAD LOAD)
            (MULTDIV MULTDIV)
            RESERVEDINSTRUCTION
            (SYNC (UNSIGNED-BYTE 5))
            SYSCALL (SHIFT SHIFT)
            (STORE STORE)
            (TRAP TRAP)))

(CONSTRUCT EXCEPTION
           (NOEXCEPTION (UNPREDICTABLE STY)))

(DEFSTOBJ+ ST$ (BRANCHSTATUS)
           CP0
           (HI :TYPE (UNSIGNED-BYTE 64)
               :INITIALLY 0)
           HLSTATUS (LLBIT)
           (LO :TYPE (UNSIGNED-BYTE 64)
               :INITIALLY 0)
           (MEM :TYPE (ARRAY (UNSIGNED-BYTE 8)
                             (18446744073709551616))
                :INITIALLY 0)
           (PC :TYPE (UNSIGNED-BYTE 64)
               :INITIALLY 0)
           EXCEPTION
           (GPREGS :TYPE (ARRAY (UNSIGNED-BYTE 64) (32))
                   :INITIALLY 0))

(VALUE-TRIPLE "See l3.lisp for the definition of raise-exception")

(PROGRAM)

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "reg'StatusRegister"
   (VAR "x" (CTY "StatusRegister"))
   (CS (VAR "x" (CTY "StatusRegister"))
       (SQBKT ((REC (CTY "StatusRegister")
                    (SQBKT (VAR "'rst" (FTY 23))
                           (VAR "BEV" BTY)
                           (VAR "ERL" BTY)
                           (VAR "EXL" BTY)
                           (VAR "IE" BTY)
                           (VAR "IM0" BTY)
                           (VAR "IM1" BTY)
                           (VAR "KSU" (FTY 2))
                           (VAR "RE" BTY)))
               (BOP MDFY
                    (CLOSE (TP (SQBKT (VAR "i" NTY) (AVAR BTY)))
                           (ITB (SQBKT ((EQ (VAR "i" NTY) (LN 31))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 4)))
                                       ((EQ (VAR "i" NTY) (LN 30))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 3)))
                                       ((EQ (VAR "i" NTY) (LN 29))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 2)))
                                       ((EQ (VAR "i" NTY) (LN 28))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 1)))
                                       ((EQ (VAR "i" NTY) (LN 27))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 0)))
                                       ((EQ (VAR "i" NTY) (LN 26))
                                        (VAR "RE" BTY))
                                       ((EQ (VAR "i" NTY) (LN 25))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 7)))
                                       ((EQ (VAR "i" NTY) (LN 24))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 6)))
                                       ((EQ (VAR "i" NTY) (LN 23))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 5)))
                                       ((EQ (VAR "i" NTY) (LN 22))
                                        (VAR "BEV" BTY))
                                       ((EQ (VAR "i" NTY) (LN 21))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 19)))
                                       ((EQ (VAR "i" NTY) (LN 20))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 18)))
                                       ((EQ (VAR "i" NTY) (LN 19))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 17)))
                                       ((EQ (VAR "i" NTY) (LN 18))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 16)))
                                       ((EQ (VAR "i" NTY) (LN 17))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 15)))
                                       ((EQ (VAR "i" NTY) (LN 16))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 14)))
                                       ((EQ (VAR "i" NTY) (LN 15))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 13)))
                                       ((EQ (VAR "i" NTY) (LN 14))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 12)))
                                       ((EQ (VAR "i" NTY) (LN 13))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 11)))
                                       ((EQ (VAR "i" NTY) (LN 12))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 10)))
                                       ((EQ (VAR "i" NTY) (LN 11))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 9)))
                                       ((EQ (VAR "i" NTY) (LN 10))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 8)))
                                       ((EQ (VAR "i" NTY) (LN 9))
                                        (VAR "IM1" BTY))
                                       ((EQ (VAR "i" NTY) (LN 8))
                                        (VAR "IM0" BTY))
                                       ((EQ (VAR "i" NTY) (LN 7))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 22)))
                                       ((EQ (VAR "i" NTY) (LN 6))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 21)))
                                       ((EQ (VAR "i" NTY) (LN 5))
                                        (BOP BIT (VAR "'rst" (FTY 23)) (LN 20)))
                                       ((EQ (VAR "i" NTY) (LN 4))
                                        (BOP BIT (VAR "KSU" (FTY 2)) (LN 1)))
                                       ((EQ (VAR "i" NTY) (LN 3))
                                        (BOP BIT (VAR "KSU" (FTY 2)) (LN 0)))
                                       ((EQ (VAR "i" NTY) (LN 2))
                                        (VAR "ERL" BTY))
                                       ((EQ (VAR "i" NTY) (LN 1))
                                        (VAR "EXL" BTY)))
                                (VAR "IE" BTY)))
                    (LW 0 32))))))))

(VALUE-TRIPLE
   (LIST :ERROR (DEF "rec'StatusRegister" (VAR "x" F32)
                     (REC (CTY "StatusRegister")
                          (SQBKT CC
                                 (SQBKT (EX (VAR "x" F32) (LN 7) (LN 5) (FTY 3))
                                        (EX (VAR "x" F32)
                                            (LN 21)
                                            (LN 10)
                                            (FTY 12))
                                        (EX (VAR "x" F32)
                                            (LN 25)
                                            (LN 23)
                                            (FTY 3))
                                        (EX (VAR "x" F32)
                                            (LN 31)
                                            (LN 27)
                                            (FTY 5)))
                                 (BOP BIT (VAR "x" F32) (LN 22))
                                 (BOP BIT (VAR "x" F32) (LN 2))
                                 (BOP BIT (VAR "x" F32) (LN 1))
                                 (BOP BIT (VAR "x" F32) (LN 0))
                                 (BOP BIT (VAR "x" F32) (LN 8))
                                 (BOP BIT (VAR "x" F32) (LN 9))
                                 (EX (VAR "x" F32) (LN 4) (LN 3) (FTY 2))
                                 (BOP BIT (VAR "x" F32) (LN 26)))))))

(VALUE-TRIPLE (LIST :ERROR (DEF "write'rec'StatusRegister"
                                (TP (SQBKT (AVAR F32)
                                           (VAR "x" (CTY "StatusRegister"))))
                                (CALL "reg'StatusRegister"
                                      F32 (VAR "x" (CTY "StatusRegister"))))))

(VALUE-TRIPLE (LIST :ERROR (DEF "write'reg'StatusRegister"
                                (TP (SQBKT (AVAR (CTY "StatusRegister"))
                                           (VAR "x" F32)))
                                (CALL "rec'StatusRegister"
                                      (CTY "StatusRegister")
                                      (VAR "x" F32)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "reg'ConfigRegister"
   (VAR "x" (CTY "ConfigRegister"))
   (CS (VAR "x" (CTY "ConfigRegister"))
       (SQBKT ((REC (CTY "ConfigRegister")
                    (SQBKT (VAR "'rst" (FTY 31))
                           (VAR "BE" BTY)))
               (BOP MDFY
                    (CLOSE (TP (SQBKT (VAR "i" NTY) (AVAR BTY)))
                           (ITB (SQBKT ((EQ (VAR "i" NTY) (LN 31))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 15)))
                                       ((EQ (VAR "i" NTY) (LN 30))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 14)))
                                       ((EQ (VAR "i" NTY) (LN 29))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 13)))
                                       ((EQ (VAR "i" NTY) (LN 28))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 12)))
                                       ((EQ (VAR "i" NTY) (LN 27))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 11)))
                                       ((EQ (VAR "i" NTY) (LN 26))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 10)))
                                       ((EQ (VAR "i" NTY) (LN 25))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 9)))
                                       ((EQ (VAR "i" NTY) (LN 24))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 8)))
                                       ((EQ (VAR "i" NTY) (LN 23))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 7)))
                                       ((EQ (VAR "i" NTY) (LN 22))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 6)))
                                       ((EQ (VAR "i" NTY) (LN 21))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 5)))
                                       ((EQ (VAR "i" NTY) (LN 20))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 4)))
                                       ((EQ (VAR "i" NTY) (LN 19))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 3)))
                                       ((EQ (VAR "i" NTY) (LN 18))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 2)))
                                       ((EQ (VAR "i" NTY) (LN 17))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 1)))
                                       ((EQ (VAR "i" NTY) (LN 16))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 0)))
                                       ((EQ (VAR "i" NTY) (LN 15))
                                        (VAR "BE" BTY))
                                       ((EQ (VAR "i" NTY) (LN 14))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 30)))
                                       ((EQ (VAR "i" NTY) (LN 13))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 29)))
                                       ((EQ (VAR "i" NTY) (LN 12))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 28)))
                                       ((EQ (VAR "i" NTY) (LN 11))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 27)))
                                       ((EQ (VAR "i" NTY) (LN 10))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 26)))
                                       ((EQ (VAR "i" NTY) (LN 9))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 25)))
                                       ((EQ (VAR "i" NTY) (LN 8))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 24)))
                                       ((EQ (VAR "i" NTY) (LN 7))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 23)))
                                       ((EQ (VAR "i" NTY) (LN 6))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 22)))
                                       ((EQ (VAR "i" NTY) (LN 5))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 21)))
                                       ((EQ (VAR "i" NTY) (LN 4))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 20)))
                                       ((EQ (VAR "i" NTY) (LN 3))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 19)))
                                       ((EQ (VAR "i" NTY) (LN 2))
                                        (BOP BIT (VAR "'rst" (FTY 31)) (LN 18)))
                                       ((EQ (VAR "i" NTY) (LN 1))
                                        (BOP BIT (VAR "'rst" (FTY 31))
                                             (LN 17))))
                                (BOP BIT (VAR "'rst" (FTY 31))
                                     (LN 16))))
                    (LW 0 32))))))))

(VALUE-TRIPLE
    (LIST :ERROR (DEF "rec'ConfigRegister" (VAR "x" F32)
                      (REC (CTY "ConfigRegister")
                           (SQBKT CC
                                  (SQBKT (EX (VAR "x" F32)
                                             (LN 14)
                                             (LN 0)
                                             (FTY 15))
                                         (EX (VAR "x" F32) (LN 31) (LN 16) F16))
                                  (BOP BIT (VAR "x" F32) (LN 15)))))))

(VALUE-TRIPLE (LIST :ERROR (DEF "write'rec'ConfigRegister"
                                (TP (SQBKT (AVAR F32)
                                           (VAR "x" (CTY "ConfigRegister"))))
                                (CALL "reg'ConfigRegister"
                                      F32 (VAR "x" (CTY "ConfigRegister"))))))

(VALUE-TRIPLE (LIST :ERROR (DEF "write'reg'ConfigRegister"
                                (TP (SQBKT (AVAR (CTY "ConfigRegister"))
                                           (VAR "x" F32)))
                                (CALL "rec'ConfigRegister"
                                      (CTY "ConfigRegister")
                                      (VAR "x" F32)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "reg'CauseRegister"
   (VAR "x" (CTY "CauseRegister"))
   (CS (VAR "x" (CTY "CauseRegister"))
       (SQBKT ((REC (CTY "CauseRegister")
                    (SQBKT (VAR "'rst" (FTY 27))
                           (VAR "ExcCode" (FTY 5))))
               (BOP MDFY
                    (CLOSE (TP (SQBKT (VAR "i" NTY) (AVAR BTY)))
                           (ITB (SQBKT ((EQ (VAR "i" NTY) (LN 31))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 24)))
                                       ((EQ (VAR "i" NTY) (LN 30))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 23)))
                                       ((EQ (VAR "i" NTY) (LN 29))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 22)))
                                       ((EQ (VAR "i" NTY) (LN 28))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 21)))
                                       ((EQ (VAR "i" NTY) (LN 27))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 20)))
                                       ((EQ (VAR "i" NTY) (LN 26))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 19)))
                                       ((EQ (VAR "i" NTY) (LN 25))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 18)))
                                       ((EQ (VAR "i" NTY) (LN 24))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 17)))
                                       ((EQ (VAR "i" NTY) (LN 23))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 16)))
                                       ((EQ (VAR "i" NTY) (LN 22))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 15)))
                                       ((EQ (VAR "i" NTY) (LN 21))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 14)))
                                       ((EQ (VAR "i" NTY) (LN 20))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 13)))
                                       ((EQ (VAR "i" NTY) (LN 19))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 12)))
                                       ((EQ (VAR "i" NTY) (LN 18))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 11)))
                                       ((EQ (VAR "i" NTY) (LN 17))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 10)))
                                       ((EQ (VAR "i" NTY) (LN 16))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 9)))
                                       ((EQ (VAR "i" NTY) (LN 15))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 8)))
                                       ((EQ (VAR "i" NTY) (LN 14))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 7)))
                                       ((EQ (VAR "i" NTY) (LN 13))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 6)))
                                       ((EQ (VAR "i" NTY) (LN 12))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 5)))
                                       ((EQ (VAR "i" NTY) (LN 11))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 4)))
                                       ((EQ (VAR "i" NTY) (LN 10))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 3)))
                                       ((EQ (VAR "i" NTY) (LN 9))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 2)))
                                       ((EQ (VAR "i" NTY) (LN 8))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 1)))
                                       ((EQ (VAR "i" NTY) (LN 7))
                                        (BOP BIT (VAR "'rst" (FTY 27)) (LN 0)))
                                       ((EQ (VAR "i" NTY) (LN 6))
                                        (BOP BIT (VAR "ExcCode" (FTY 5))
                                             (LN 4)))
                                       ((EQ (VAR "i" NTY) (LN 5))
                                        (BOP BIT (VAR "ExcCode" (FTY 5))
                                             (LN 3)))
                                       ((EQ (VAR "i" NTY) (LN 4))
                                        (BOP BIT (VAR "ExcCode" (FTY 5))
                                             (LN 2)))
                                       ((EQ (VAR "i" NTY) (LN 3))
                                        (BOP BIT (VAR "ExcCode" (FTY 5))
                                             (LN 1)))
                                       ((EQ (VAR "i" NTY) (LN 2))
                                        (BOP BIT (VAR "ExcCode" (FTY 5))
                                             (LN 0)))
                                       ((EQ (VAR "i" NTY) (LN 1))
                                        (BOP BIT (VAR "'rst" (FTY 27))
                                             (LN 26))))
                                (BOP BIT (VAR "'rst" (FTY 27))
                                     (LN 25))))
                    (LW 0 32))))))))

(VALUE-TRIPLE
   (LIST :ERROR (DEF "rec'CauseRegister" (VAR "x" F32)
                     (REC (CTY "CauseRegister")
                          (SQBKT CC
                                 (SQBKT (EX (VAR "x" F32) (LN 1) (LN 0) (FTY 2))
                                        (EX (VAR "x" F32)
                                            (LN 31)
                                            (LN 7)
                                            (FTY 25)))
                                 (EX (VAR "x" F32)
                                     (LN 6)
                                     (LN 2)
                                     (FTY 5)))))))

(VALUE-TRIPLE (LIST :ERROR (DEF "write'rec'CauseRegister"
                                (TP (SQBKT (AVAR F32)
                                           (VAR "x" (CTY "CauseRegister"))))
                                (CALL "reg'CauseRegister"
                                      F32 (VAR "x" (CTY "CauseRegister"))))))

(VALUE-TRIPLE (LIST :ERROR (DEF "write'reg'CauseRegister"
                                (TP (SQBKT (AVAR (CTY "CauseRegister"))
                                           (VAR "x" F32)))
                                (CALL "rec'CauseRegister"
                                      (CTY "CauseRegister")
                                      (VAR "x" F32)))))

(DEFUN-STRUCT WRITE-GPR
              (((VALUE (UNSIGNED-BYTE-P 64 VALUE))
                (N (UNSIGNED-BYTE-P 5 N)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LET ((ST$ (IF (NOT (EQL N 0))
                             (UPDATE-GPREGSI N VALUE ST$)
                             ST$)))
                   (MV (UNIT-VALUE) ST$)))

(DEFUN-STRUCT GPR ((N (UNSIGNED-BYTE-P 5 N)) ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (MV (IF (EQL N 0) 0 (GPREGSI N ST$))
                  ST$))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "write'CPR"
   (TP (SQBKT (VAR "value" F64)
              (VAR "n" NTY)
              (VAR "reg" (FTY 5))
              (VAR "sel" (FTY 3))))
   (CLOSE
    QVAR
    (CS
     (TP (SQBKT (VAR "n" NTY)
                (VAR "reg" (FTY 5))
                (VAR "sel" (FTY 3))))
     (SQBKT
      ((TP (SQBKT LN 0 (LW 9 5) (LW 0 3)))
       (TP
          (SQBKT LU
                 (RUPD "CP0"
                       (TP (SQBKT QVAR
                                  (RUPD "Count"
                                        (TP (SQBKT (DEST "CP0" (CTY "CP0") QVAR)
                                                   (EX (VAR "value" F64)
                                                       (LN 31)
                                                       (LN 0)
                                                       F32))))))))))
      ((TP (SQBKT LN 0 (LW 12 5) (LW 0 3)))
       (LET
        (VAR "v" (CTY "CP0"))
        (DEST "CP0" (CTY "CP0") QVAR)
        (TP
         (SQBKT
          LU
          (RUPD
           "CP0"
           (TP
            (SQBKT
             QVAR
             (RUPD
               "Status"
               (TP (SQBKT (VAR "v" (CTY "CP0"))
                          (CALL "write'reg'StatusRegister"
                                (CTY "StatusRegister")
                                (TP (SQBKT (DEST "Status" (CTY "StatusRegister")
                                                 (VAR "v" (CTY "CP0")))
                                           (EX (VAR "value" F64)
                                               (LN 31)
                                               (LN 0)
                                               F32))))))))))))))
      ((TP (SQBKT LN 0 (LW 13 5) (LW 0 3)))
       (LET
        (VAR "v" (CTY "CP0"))
        (DEST "CP0" (CTY "CP0") QVAR)
        (TP
         (SQBKT
          LU
          (RUPD
           "CP0"
           (TP
            (SQBKT
             QVAR
             (RUPD
                 "Cause"
                 (TP (SQBKT (VAR "v" (CTY "CP0"))
                            (CALL "write'reg'CauseRegister"
                                  (CTY "CauseRegister")
                                  (TP (SQBKT (DEST "Cause" (CTY "CauseRegister")
                                                   (VAR "v" (CTY "CP0")))
                                             (EX (VAR "value" F64)
                                                 (LN 31)
                                                 (LN 0)
                                                 F32))))))))))))))
      ((TP (SQBKT LN 0 (LW 14 5) (LW 0 3)))
       (TP
          (SQBKT LU
                 (RUPD "CP0"
                       (TP (SQBKT QVAR
                                  (RUPD "EPC"
                                        (TP (SQBKT (DEST "CP0" (CTY "CP0") QVAR)
                                                   (VAR "value" F64))))))))))
      ((TP (SQBKT LN 0 (LW 16 5) (LW 0 3)))
       (LET
        (VAR "v" (CTY "CP0"))
        (DEST "CP0" (CTY "CP0") QVAR)
        (TP
         (SQBKT
          LU
          (RUPD
           "CP0"
           (TP
            (SQBKT
             QVAR
             (RUPD
               "Config"
               (TP (SQBKT (VAR "v" (CTY "CP0"))
                          (CALL "write'reg'ConfigRegister"
                                (CTY "ConfigRegister")
                                (TP (SQBKT (DEST "Config" (CTY "ConfigRegister")
                                                 (VAR "v" (CTY "CP0")))
                                           (EX (VAR "value" F64)
                                               (LN 31)
                                               (LN 0)
                                               F32))))))))))))))
      ((TP (SQBKT LN 0 (LW 30 5) (LW 0 3)))
       (TP
          (SQBKT LU
                 (RUPD "CP0"
                       (TP (SQBKT QVAR
                                  (RUPD "ErrorEPC"
                                        (TP (SQBKT (DEST "CP0" (CTY "CP0") QVAR)
                                                   (VAR "value" F64))))))))))
      ((AVAR (PTY NTY (PTY (FTY 5) (FTY 3))))
       (TP (SQBKT LU QVAR)))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "CPR"
   (TP (SQBKT (VAR "n" NTY)
              (VAR "reg" (FTY 5))
              (VAR "sel" (FTY 3))))
   (CLOSE
        QVAR
        (CS (TP (SQBKT (VAR "n" NTY)
                       (VAR "reg" (FTY 5))
                       (VAR "sel" (FTY 3))))
            (SQBKT ((TP (SQBKT LN 0 (LW 9 5) (LW 0 3)))
                    (TP (SQBKT (MOP (CAST F64)
                                    (DEST "Count"
                                          F32 (DEST "CP0" (CTY "CP0") QVAR)))
                               QVAR)))
                   ((TP (SQBKT LN 0 (LW 12 5) (LW 0 3)))
                    (TP (SQBKT (MOP (CAST F64)
                                    (CALL "reg'StatusRegister" F32
                                          (DEST "Status" (CTY "StatusRegister")
                                                (DEST "CP0" (CTY "CP0") QVAR))))
                               QVAR)))
                   ((TP (SQBKT LN 0 (LW 13 5) (LW 0 3)))
                    (TP (SQBKT (MOP (CAST F64)
                                    (CALL "reg'CauseRegister" F32
                                          (DEST "Cause" (CTY "CauseRegister")
                                                (DEST "CP0" (CTY "CP0") QVAR))))
                               QVAR)))
                   ((TP (SQBKT LN 0 (LW 14 5) (LW 0 3)))
                    (TP (SQBKT (DEST "EPC" F64 (DEST "CP0" (CTY "CP0") QVAR))
                               QVAR)))
                   ((TP (SQBKT LN 0 (LW 16 5) (LW 0 3)))
                    (TP (SQBKT (MOP (CAST F64)
                                    (CALL "reg'ConfigRegister" F32
                                          (DEST "Config" (CTY "ConfigRegister")
                                                (DEST "CP0" (CTY "CP0") QVAR))))
                               QVAR)))
                   ((TP (SQBKT LN 0 (LW 30 5) (LW 0 3)))
                    (TP (SQBKT (DEST "ErrorEPC"
                                     F64 (DEST "CP0" (CTY "CP0") QVAR))
                               QVAR)))
                   ((AVAR (PTY NTY (PTY (FTY 5) (FTY 3))))
                    (TP (SQBKT (LX F64) QVAR)))))))))

(DEFCONST *BYTE* 0)

(DEFCONST *HALFWORD* 1)

(DEFCONST *WORD* 3)

(DEFCONST *DOUBLEWORD* 7)

(DEFCONST *PSIZE* 64)

(VALUE-TRIPLE
 (LIST
    :ERROR
    (DEF "UserMode" QVAR
         (TP (SQBKT (BOP AND
                         (BOP AND
                              (EQ (DEST "KSU" (FTY 2)
                                        (DEST "Status" (CTY "StatusRegister")
                                              (DEST "CP0" (CTY "CP0") QVAR)))
                                  (LW 2 2))
                              (MOP NOT
                                   (DEST "EXL" BTY
                                         (DEST "Status" (CTY "StatusRegister")
                                               (DEST "CP0" (CTY "CP0") QVAR)))))
                         (MOP NOT
                              (DEST "ERL" BTY
                                    (DEST "Status" (CTY "StatusRegister")
                                          (DEST "CP0" (CTY "CP0") QVAR)))))
                    QVAR)))))

(VALUE-TRIPLE
     (LIST :ERROR (DEF "BigEndianMem" QVAR
                       (TP (SQBKT (DEST "BE" BTY
                                        (DEST "Config" (CTY "ConfigRegister")
                                              (DEST "CP0" (CTY "CP0") QVAR)))
                                  QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
     "ReverseEndian" QVAR
     (TP (SQBKT (MOP (CAST F1)
                     (BOP AND
                          (DEST "RE" BTY
                                (DEST "Status" (CTY "StatusRegister")
                                      (DEST "CP0" (CTY "CP0") QVAR)))
                          (MOP FST
                               (APPLY (CONST "UserMode" (ATY QTY (PTY BTY QTY)))
                                      QVAR))))
                QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "BigEndianCPU" QVAR
   (TP
     (SQBKT (BOP BXOR
                 (MOP (CAST F1)
                      (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR)))
                 (MOP FST
                      (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                             QVAR)))
            QVAR)))))

(VALUE-TRIPLE (LIST :ERROR (DEF "AddressTranslation"
                                (TP (SQBKT (VAR "vAddr" F64)
                                           (VAR "IorD" (CTY "IorD"))
                                           (VAR "LorS" (CTY "LorS"))))
                                (TP (SQBKT (VAR "vAddr" F64)
                                           (LX (FTY 3)))))))

(DEFUN-STRUCT LOADMEMORY
              (((CCA (UNSIGNED-BYTE-P 3 CCA))
                (ACCESSLENGTH (UNSIGNED-BYTE-P 3 ACCESSLENGTH))
                (PADDR (UNSIGNED-BYTE-P 64 PADDR))
                (VADDR (UNSIGNED-BYTE-P 64 VADDR))
                (IORD (TYPE-IORD IORD)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LET ((A (LOGAND PADDR (LOGNOT 7))))
                   (MV (IF (EQL (CAR (BIGENDIANCPU ST$)) 1)
                           (CAT (MEMI A ST$)
                                8 (MEMI (N+ 64 A 1) ST$)
                                8 (MEMI (N+ 64 A 2) ST$)
                                8 (MEMI (N+ 64 A 3) ST$)
                                8 (MEMI (N+ 64 A 4) ST$)
                                8 (MEMI (N+ 64 A 5) ST$)
                                8 (MEMI (N+ 64 A 6) ST$)
                                8 (MEMI (N+ 64 A 7) ST$)
                                8)
                           (CAT (MEMI (N+ 64 A 7) ST$)
                                8 (MEMI (N+ 64 A 6) ST$)
                                8 (MEMI (N+ 64 A 5) ST$)
                                8 (MEMI (N+ 64 A 4) ST$)
                                8 (MEMI (N+ 64 A 3) ST$)
                                8 (MEMI (N+ 64 A 2) ST$)
                                8 (MEMI (N+ 64 A 1) ST$)
                                8 (MEMI A ST$)
                                8))
                       ST$)))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "StoreMemory"
   (TP (SQBKT (VAR "CCA" (FTY 3))
              (VAR "AccessLength" (FTY 3))
              (VAR "MemElem" F64)
              (VAR "pAddr" F64)
              (VAR "vAddr" F64)
              (VAR "IorD" (CTY "IorD"))))
   (CLOSE
    QVAR
    (LET
     (VAR "a" F64)
     (BOP BAND (VAR "pAddr" F64)
          (MOP BNOT (LW 7 64)))
     (LET
      (VAR "l" (FTY 3))
      (EX (VAR "vAddr" F64)
          (LN 2)
          (LN 0)
          (FTY 3))
      (LET
       (VAR "h" (FTY 3))
       (BOP ADD (VAR "l" (FTY 3))
            (VAR "AccessLength" (FTY 3)))
       (ITE
        (EQ (MOP FST
                 (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                        QVAR))
            (LW 1 1))
        (LET
         QVAR
         (ITE (EQ (VAR "l" (FTY 3)) (LW 0 3))
              (RUPD "MEM"
                    (TP (SQBKT QVAR
                               (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                     (VAR "a" F64)
                                     (EX (VAR "MemElem" F64)
                                         (LN 63)
                                         (LN 56)
                                         F8)))))
              QVAR)
         (LET
          QVAR
          (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 1 3))
                    (BOP ULE (LW 1 3) (VAR "h" (FTY 3))))
               (RUPD "MEM"
                     (TP (SQBKT QVAR
                                (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                      (BOP ADD (VAR "a" F64) (LW 1 64))
                                      (EX (VAR "MemElem" F64)
                                          (LN 55)
                                          (LN 48)
                                          F8)))))
               QVAR)
          (LET
           QVAR
           (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 2 3))
                     (BOP ULE (LW 2 3) (VAR "h" (FTY 3))))
                (RUPD "MEM"
                      (TP (SQBKT QVAR
                                 (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                       (BOP ADD (VAR "a" F64) (LW 2 64))
                                       (EX (VAR "MemElem" F64)
                                           (LN 47)
                                           (LN 40)
                                           F8)))))
                QVAR)
           (LET
            QVAR
            (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 3 3))
                      (BOP ULE (LW 3 3) (VAR "h" (FTY 3))))
                 (RUPD "MEM"
                       (TP (SQBKT QVAR
                                  (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                        (BOP ADD (VAR "a" F64) (LW 3 64))
                                        (EX (VAR "MemElem" F64)
                                            (LN 39)
                                            (LN 32)
                                            F8)))))
                 QVAR)
            (LET
             QVAR
             (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 4 3))
                       (BOP ULE (LW 4 3) (VAR "h" (FTY 3))))
                  (RUPD "MEM"
                        (TP (SQBKT QVAR
                                   (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                         (BOP ADD (VAR "a" F64) (LW 4 64))
                                         (EX (VAR "MemElem" F64)
                                             (LN 31)
                                             (LN 24)
                                             F8)))))
                  QVAR)
             (LET
              QVAR
              (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 5 3))
                        (BOP ULE (LW 5 3) (VAR "h" (FTY 3))))
                   (RUPD "MEM"
                         (TP (SQBKT QVAR
                                    (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                          (BOP ADD (VAR "a" F64) (LW 5 64))
                                          (EX (VAR "MemElem" F64)
                                              (LN 23)
                                              (LN 16)
                                              F8)))))
                   QVAR)
              (LET
               QVAR
               (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 6 3))
                         (BOP ULE (LW 6 3) (VAR "h" (FTY 3))))
                    (RUPD "MEM"
                          (TP (SQBKT QVAR
                                     (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                           (BOP ADD (VAR "a" F64) (LW 6 64))
                                           (EX (VAR "MemElem" F64)
                                               (LN 15)
                                               (LN 8)
                                               F8)))))
                    QVAR)
               (TP
                (SQBKT
                   LU
                   (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 7 3))
                             (BOP ULE (LW 7 3) (VAR "h" (FTY 3))))
                        (RUPD "MEM"
                              (TP (SQBKT QVAR
                                         (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                               (BOP ADD (VAR "a" F64) (LW 7 64))
                                               (EX (VAR "MemElem" F64)
                                                   (LN 7)
                                                   (LN 0)
                                                   F8)))))
                        QVAR))))))))))
        (LET
         QVAR
         (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 7 3))
                   (BOP ULE (LW 7 3) (VAR "h" (FTY 3))))
              (RUPD "MEM"
                    (TP (SQBKT QVAR
                               (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                     (BOP ADD (VAR "a" F64) (LW 7 64))
                                     (EX (VAR "MemElem" F64)
                                         (LN 63)
                                         (LN 56)
                                         F8)))))
              QVAR)
         (LET
          QVAR
          (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 6 3))
                    (BOP ULE (LW 6 3) (VAR "h" (FTY 3))))
               (RUPD "MEM"
                     (TP (SQBKT QVAR
                                (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                      (BOP ADD (VAR "a" F64) (LW 6 64))
                                      (EX (VAR "MemElem" F64)
                                          (LN 55)
                                          (LN 48)
                                          F8)))))
               QVAR)
          (LET
           QVAR
           (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 5 3))
                     (BOP ULE (LW 5 3) (VAR "h" (FTY 3))))
                (RUPD "MEM"
                      (TP (SQBKT QVAR
                                 (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                       (BOP ADD (VAR "a" F64) (LW 5 64))
                                       (EX (VAR "MemElem" F64)
                                           (LN 47)
                                           (LN 40)
                                           F8)))))
                QVAR)
           (LET
            QVAR
            (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 4 3))
                      (BOP ULE (LW 4 3) (VAR "h" (FTY 3))))
                 (RUPD "MEM"
                       (TP (SQBKT QVAR
                                  (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                        (BOP ADD (VAR "a" F64) (LW 4 64))
                                        (EX (VAR "MemElem" F64)
                                            (LN 39)
                                            (LN 32)
                                            F8)))))
                 QVAR)
            (LET
             QVAR
             (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 3 3))
                       (BOP ULE (LW 3 3) (VAR "h" (FTY 3))))
                  (RUPD "MEM"
                        (TP (SQBKT QVAR
                                   (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                         (BOP ADD (VAR "a" F64) (LW 3 64))
                                         (EX (VAR "MemElem" F64)
                                             (LN 31)
                                             (LN 24)
                                             F8)))))
                  QVAR)
             (LET
              QVAR
              (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 2 3))
                        (BOP ULE (LW 2 3) (VAR "h" (FTY 3))))
                   (RUPD "MEM"
                         (TP (SQBKT QVAR
                                    (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                          (BOP ADD (VAR "a" F64) (LW 2 64))
                                          (EX (VAR "MemElem" F64)
                                              (LN 23)
                                              (LN 16)
                                              F8)))))
                   QVAR)
              (LET
               QVAR
               (ITE (BOP AND (BOP ULE (VAR "l" (FTY 3)) (LW 1 3))
                         (BOP ULE (LW 1 3) (VAR "h" (FTY 3))))
                    (RUPD "MEM"
                          (TP (SQBKT QVAR
                                     (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                           (BOP ADD (VAR "a" F64) (LW 1 64))
                                           (EX (VAR "MemElem" F64)
                                               (LN 15)
                                               (LN 8)
                                               F8)))))
                    QVAR)
               (TP
                 (SQBKT
                      LU
                      (ITE (EQ (VAR "l" (FTY 3)) (LW 0 3))
                           (RUPD "MEM"
                                 (TP (SQBKT QVAR
                                            (FUPD (DEST "MEM" (ATY F64 F8) QVAR)
                                                  (VAR "a" F64)
                                                  (EX (VAR "MemElem" F64)
                                                      (LN 7)
                                                      (LN 0)
                                                      F8)))))
                           QVAR))))))))))))))))))

(DEFUN-STRUCT EXCEPTIONCODE
              ((EXCEPTIONTYPE (TYPE-EXCEPTIONTYPE EXCEPTIONTYPE)))
              (CASE-MATCH+ EXCEPTIONTYPE ('ADEL 4)
                           ('ADES 5)
                           ('SYS 8)
                           ('BP 9)
                           ('RI 10)
                           ('OV 12)
                           ('TR 13)
                           (& (IMPOSSIBLE (ARB (UNSIGNED-BYTE 5))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "SignalException"
   (VAR "ExceptionType" (CTY "ExceptionType"))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (MOP NOT
               (DEST "EXL" BTY
                     (DEST "Status" (CTY "StatusRegister")
                           (DEST "CP0" (CTY "CP0") QVAR))))
          (RUPD "CP0"
                (TP (SQBKT QVAR
                           (RUPD "EPC"
                                 (TP (SQBKT (DEST "CP0" (CTY "CP0") QVAR)
                                            (DEST "PC" F64 QVAR)))))))
          QVAR)
     (LET
      (VAR "v" (CTY "CP0"))
      (DEST "CP0" (CTY "CP0") QVAR)
      (LET
       QVAR
       (RUPD
        "CP0"
        (TP
         (SQBKT
          QVAR
          (RUPD
           "Cause"
           (TP
             (SQBKT (VAR "v" (CTY "CP0"))
                    (RUPD "ExcCode"
                          (TP (SQBKT (DEST "Cause" (CTY "CauseRegister")
                                           (VAR "v" (CTY "CP0")))
                                     (CALL "ExceptionCode" (FTY 5)
                                           (VAR "ExceptionType"
                                                (CTY "ExceptionType"))))))))))))
       (LET
        (VAR "v" (CTY "CP0"))
        (DEST "CP0" (CTY "CP0") QVAR)
        (LET
         QVAR
         (RUPD
          "CP0"
          (TP
           (SQBKT
            QVAR
            (RUPD
               "Status"
               (TP (SQBKT (VAR "v" (CTY "CP0"))
                          (RUPD "EXL"
                                (TP (SQBKT (DEST "Status" (CTY "StatusRegister")
                                                 (VAR "v" (CTY "CP0")))
                                           LT)))))))))
         (LET
            (VAR "v" F64)
            (ITE (DEST "BEV" BTY
                       (DEST "Status" (CTY "StatusRegister")
                             (DEST "CP0" (CTY "CP0") QVAR)))
                 (LW 18446744072631616000 64)
                 (LW 18446744071562067968 64))
            (TP (SQBKT LU
                       (RUPD "PC"
                             (TP (SQBKT QVAR CC
                                        (SQBKT (EX (VAR "v" F64)
                                                   (LN 63)
                                                   (LN 30)
                                                   (FTY 34))
                                               (BOP ADD
                                                    (EX (VAR "v" F64)
                                                        (LN 29)
                                                        (LN 0)
                                                        (FTY 30))
                                                    (LW 384 30))))))))))))))))))

(DEFUN-STRUCT NOTWORDVALUE
              ((VALUE (UNSIGNED-BYTE-P 64 VALUE)))
              (LET ((TOP (BITS VALUE 63 32)))
                   (IF (LOGBITP 64 VALUE 31)
                       (NOT (EQL TOP 4294967295))
                       (NOT (EQL TOP 0)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
      "dfn'ADDI"
      (TP (SQBKT (VAR "rs" (FTY 5))
                 (VAR "rt" (FTY 5))
                 (VAR "immediate" F16)))
      (CLOSE QVAR
             (LET QVAR
                  (ITE (CALL "NotWordValue" BTY
                             (MOP FST
                                  (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                               (VAR "rs" (FTY 5)))
                                         QVAR)))
                       (MOP SND
                            (APPLY (CALL "raise'exception"
                                         (ATY QTY (PTY UTY QTY))
                                         (CALL "UNPREDICTABLE" (CTY "exception")
                                               (LS "ADDI: NotWordValue")))
                                   QVAR))
                       QVAR)
                  (LET (VAR "v" (FTY 33))
                       (BOP ADD
                            (EX (MOP FST
                                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                  (VAR "rs" (FTY 5)))
                                            QVAR))
                                (LN 32)
                                (LN 0)
                                (FTY 33))
                            (MOP (SE (FTY 33))
                                 (VAR "immediate" F16)))
                       (ITE (MOP NOT
                                 (EQ (BOP BIT (VAR "v" (FTY 33)) (LN 32))
                                     (BOP BIT (VAR "v" (FTY 33)) (LN 31))))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Ov" (CTY "ExceptionType")))
                                   QVAR)
                            (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                         (TP (SQBKT (MOP (SE F64)
                                                         (EX (VAR "v" (FTY 33))
                                                             (LN 31)
                                                             (LN 0)
                                                             F32))
                                                    (VAR "rt" (FTY 5)))))
                                   QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'ADDIU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (CALL "NotWordValue" BTY
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR)))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "ADDIU: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (BOP ADD
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (MOP (SE F32) (VAR "immediate" F16))))
                   (VAR "rt" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
      :ERROR
      (DEF "dfn'DADDI"
           (TP (SQBKT (VAR "rs" (FTY 5))
                      (VAR "rt" (FTY 5))
                      (VAR "immediate" F16)))
           (CLOSE QVAR
                  (LET (VAR "v" (FTY 65))
                       (BOP ADD
                            (MOP (SE (FTY 65))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR)))
                            (MOP (SE (FTY 65))
                                 (VAR "immediate" F16)))
                       (ITE (MOP NOT
                                 (EQ (BOP BIT (VAR "v" (FTY 65)) (LN 64))
                                     (BOP BIT (VAR "v" (FTY 65)) (LN 63))))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Ov" (CTY "ExceptionType")))
                                   QVAR)
                            (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                         (TP (SQBKT (EX (VAR "v" (FTY 65))
                                                        (LN 63)
                                                        (LN 0)
                                                        F64)
                                                    (VAR "rt" (FTY 5)))))
                                   QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DADDIU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP ADD
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16)))
                            (VAR "rt" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SLTI"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (APPLY
      (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
            (TP (SQBKT (MOP (CAST F64)
                            (BOP LT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16))))
                       (VAR "rt" (FTY 5)))))
      QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SLTIU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (APPLY
      (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
            (TP (SQBKT (MOP (CAST F64)
                            (BOP ULT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16))))
                       (VAR "rt" (FTY 5)))))
      QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'ANDI"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP BAND
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (CAST F64) (VAR "immediate" F16)))
                            (VAR "rt" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'ORI"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP BOR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (CAST F64) (VAR "immediate" F16)))
                            (VAR "rt" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'XORI"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "immediate" F16)))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP BXOR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (CAST F64) (VAR "immediate" F16)))
                            (VAR "rt" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST :ERROR
       (DEF "dfn'LUI"
            (TP (SQBKT (VAR "rt" (FTY 5))
                       (VAR "immediate" F16)))
            (CLOSE QVAR
                   (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                (TP (SQBKT (MOP (SE F64)
                                                (CC (SQBKT (VAR "immediate" F16)
                                                           (LW 0 16))))
                                           (VAR "rt" (FTY 5)))))
                          QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
     "dfn'ADD"
     (TP (SQBKT (VAR "rs" (FTY 5))
                (VAR "rt" (FTY 5))
                (VAR "rd" (FTY 5))))
     (CLOSE QVAR
            (LET QVAR
                 (ITE (BOP OR
                           (CALL "NotWordValue" BTY
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR)))
                           (CALL "NotWordValue" BTY
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                      (MOP SND
                           (APPLY (CALL "raise'exception"
                                        (ATY QTY (PTY UTY QTY))
                                        (CALL "UNPREDICTABLE" (CTY "exception")
                                              (LS "ADD: NotWordValue")))
                                  QVAR))
                      QVAR)
                 (LET (VAR "v" (FTY 33))
                      (BOP ADD
                           (EX (MOP FST
                                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                 (VAR "rs" (FTY 5)))
                                           QVAR))
                               (LN 32)
                               (LN 0)
                               (FTY 33))
                           (EX (MOP FST
                                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                 (VAR "rt" (FTY 5)))
                                           QVAR))
                               (LN 32)
                               (LN 0)
                               (FTY 33)))
                      (ITE (MOP NOT
                                (EQ (BOP BIT (VAR "v" (FTY 33)) (LN 32))
                                    (BOP BIT (VAR "v" (FTY 33)) (LN 31))))
                           (APPLY (CALL "SignalException"
                                        (ATY QTY (PTY UTY QTY))
                                        (LC "Ov" (CTY "ExceptionType")))
                                  QVAR)
                           (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                        (TP (SQBKT (MOP (SE F64)
                                                        (EX (VAR "v" (FTY 33))
                                                            (LN 31)
                                                            (LN 0)
                                                            F32))
                                                   (VAR "rd" (FTY 5)))))
                                  QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'ADDU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (BOP OR
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rs" (FTY 5)))
                                 QVAR)))
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rt" (FTY 5)))
                                 QVAR))))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "ADDU: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (BOP ADD
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)))
                   (VAR "rd" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
     "dfn'SUB"
     (TP (SQBKT (VAR "rs" (FTY 5))
                (VAR "rt" (FTY 5))
                (VAR "rd" (FTY 5))))
     (CLOSE QVAR
            (LET QVAR
                 (ITE (BOP OR
                           (CALL "NotWordValue" BTY
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR)))
                           (CALL "NotWordValue" BTY
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                      (MOP SND
                           (APPLY (CALL "raise'exception"
                                        (ATY QTY (PTY UTY QTY))
                                        (CALL "UNPREDICTABLE" (CTY "exception")
                                              (LS "SUB: NotWordValue")))
                                  QVAR))
                      QVAR)
                 (LET (VAR "v" (FTY 33))
                      (BOP SUB
                           (EX (MOP FST
                                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                 (VAR "rs" (FTY 5)))
                                           QVAR))
                               (LN 32)
                               (LN 0)
                               (FTY 33))
                           (EX (MOP FST
                                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                 (VAR "rt" (FTY 5)))
                                           QVAR))
                               (LN 32)
                               (LN 0)
                               (FTY 33)))
                      (ITE (MOP NOT
                                (EQ (BOP BIT (VAR "v" (FTY 33)) (LN 32))
                                    (BOP BIT (VAR "v" (FTY 33)) (LN 31))))
                           (APPLY (CALL "SignalException"
                                        (ATY QTY (PTY UTY QTY))
                                        (LC "Ov" (CTY "ExceptionType")))
                                  QVAR)
                           (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                        (TP (SQBKT (MOP (SE F64)
                                                        (EX (VAR "v" (FTY 33))
                                                            (LN 31)
                                                            (LN 0)
                                                            F32))
                                                   (VAR "rd" (FTY 5)))))
                                  QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SUBU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (BOP OR
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rs" (FTY 5)))
                                 QVAR)))
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rt" (FTY 5)))
                                 QVAR))))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "SUBU: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (BOP SUB
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 32)
                                 (LN 0)
                                 (FTY 33))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 32)
                                 (LN 0)
                                 (FTY 33))))
                   (VAR "rd" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
      :ERROR
      (DEF "dfn'DADD"
           (TP (SQBKT (VAR "rs" (FTY 5))
                      (VAR "rt" (FTY 5))
                      (VAR "rd" (FTY 5))))
           (CLOSE QVAR
                  (LET (VAR "v" (FTY 65))
                       (BOP ADD
                            (MOP (SE (FTY 65))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR)))
                            (MOP (SE (FTY 65))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                       (ITE (MOP NOT
                                 (EQ (BOP BIT (VAR "v" (FTY 65)) (LN 64))
                                     (BOP BIT (VAR "v" (FTY 65)) (LN 63))))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Ov" (CTY "ExceptionType")))
                                   QVAR)
                            (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                         (TP (SQBKT (EX (VAR "v" (FTY 65))
                                                        (LN 63)
                                                        (LN 0)
                                                        F64)
                                                    (VAR "rd" (FTY 5)))))
                                   QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DADDU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP ADD
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
      :ERROR
      (DEF "dfn'DSUB"
           (TP (SQBKT (VAR "rs" (FTY 5))
                      (VAR "rt" (FTY 5))
                      (VAR "rd" (FTY 5))))
           (CLOSE QVAR
                  (LET (VAR "v" (FTY 65))
                       (BOP SUB
                            (MOP (SE (FTY 65))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR)))
                            (MOP (SE (FTY 65))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                       (ITE (MOP NOT
                                 (EQ (BOP BIT (VAR "v" (FTY 65)) (LN 64))
                                     (BOP BIT (VAR "v" (FTY 65)) (LN 63))))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Ov" (CTY "ExceptionType")))
                                   QVAR)
                            (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                         (TP (SQBKT (EX (VAR "v" (FTY 65))
                                                        (LN 63)
                                                        (LN 0)
                                                        F64)
                                                    (VAR "rd" (FTY 5)))))
                                   QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSUBU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP SUB
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SLT"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
      (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
            (TP (SQBKT (MOP (CAST F64)
                            (BOP LT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                       (VAR "rd" (FTY 5)))))
      QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SLTU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
      (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
            (TP (SQBKT (MOP (CAST F64)
                            (BOP ULT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                       (VAR "rd" (FTY 5)))))
      QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'AND"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP BAND
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'OR"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP BOR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'XOR"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP BXOR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'NOR"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
      (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
            (TP (SQBKT (MOP BNOT
                            (BOP BOR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))
                       (VAR "rd" (FTY 5)))))
      QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'MULT"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (BOP OR
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rs" (FTY 5)))
                                 QVAR)))
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rt" (FTY 5)))
                                 QVAR))))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "MULT: NotWordValue")))
                      QVAR))
          QVAR)
     (LET
      (VAR "v" F64)
      (BOP MUL
           (MOP (SE F64)
                (EX (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rs" (FTY 5)))
                                QVAR))
                    (LN 31)
                    (LN 0)
                    F32))
           (MOP (SE F64)
                (EX (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rt" (FTY 5)))
                                QVAR))
                    (LN 31)
                    (LN 0)
                    F32)))
      (TP
       (SQBKT
        LU
        (RUPD
             "HLStatus"
             (TP (SQBKT (RUPD "HI"
                              (TP (SQBKT (RUPD "LO"
                                               (TP (SQBKT QVAR
                                                          (MOP (SE F64)
                                                               (EX (VAR "v" F64)
                                                                   (LN 31)
                                                                   (LN 0)
                                                                   F32)))))
                                         (MOP (SE F64)
                                              (EX (VAR "v" F64)
                                                  (LN 63)
                                                  (LN 32)
                                                  F32)))))
                        (LC "HLarith" (CTY "HLStatus")))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'MULTU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (BOP OR
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rs" (FTY 5)))
                                 QVAR)))
               (CALL "NotWordValue" BTY
                     (MOP FST
                          (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                       (VAR "rt" (FTY 5)))
                                 QVAR))))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "MULTU: NotWordValue")))
                      QVAR))
          QVAR)
     (LET
      (VAR "v" F64)
      (BOP MUL
           (MOP (CAST F64)
                (EX (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rs" (FTY 5)))
                                QVAR))
                    (LN 31)
                    (LN 0)
                    F32))
           (MOP (CAST F64)
                (EX (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rt" (FTY 5)))
                                QVAR))
                    (LN 31)
                    (LN 0)
                    F32)))
      (TP
       (SQBKT
        LU
        (RUPD
             "HLStatus"
             (TP (SQBKT (RUPD "HI"
                              (TP (SQBKT (RUPD "LO"
                                               (TP (SQBKT QVAR
                                                          (MOP (SE F64)
                                                               (EX (VAR "v" F64)
                                                                   (LN 31)
                                                                   (LN 0)
                                                                   F32)))))
                                         (MOP (SE F64)
                                              (EX (VAR "v" F64)
                                                  (LN 63)
                                                  (LN 32)
                                                  F32)))))
                        (LC "HLarith" (CTY "HLStatus")))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DMULT"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     (VAR "v" (FTY 128))
     (BOP MUL
          (MOP (SE (FTY 128))
               (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rs" (FTY 5)))
                           QVAR)))
          (MOP (SE (FTY 128))
               (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rt" (FTY 5)))
                           QVAR))))
     (TP
      (SQBKT
       LU
       (RUPD
            "HLStatus"
            (TP (SQBKT (RUPD "HI"
                             (TP (SQBKT (RUPD "LO"
                                              (TP (SQBKT QVAR
                                                         (EX (VAR "v" (FTY 128))
                                                             (LN 63)
                                                             (LN 0)
                                                             F64))))
                                        (EX (VAR "v" (FTY 128))
                                            (LN 127)
                                            (LN 64)
                                            F64))))
                       (LC "HLarith" (CTY "HLStatus"))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DMULTU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     (VAR "v" (FTY 128))
     (BOP MUL
          (MOP (CAST (FTY 128))
               (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rs" (FTY 5)))
                           QVAR)))
          (MOP (CAST (FTY 128))
               (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rt" (FTY 5)))
                           QVAR))))
     (TP
      (SQBKT
       LU
       (RUPD
            "HLStatus"
            (TP (SQBKT (RUPD "HI"
                             (TP (SQBKT (RUPD "LO"
                                              (TP (SQBKT QVAR
                                                         (EX (VAR "v" (FTY 128))
                                                             (LN 63)
                                                             (LN 0)
                                                             F64))))
                                        (EX (VAR "v" (FTY 128))
                                            (LN 127)
                                            (LN 64)
                                            F64))))
                       (LC "HLarith" (CTY "HLStatus"))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DIV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (EQ (MOP FST
                   (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                (VAR "rt" (FTY 5)))
                          QVAR))
              (LW 0 64))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "DIV: divide by zero")))
                      QVAR))
          QVAR)
     (LET
      QVAR
      (ITE (BOP OR
                (CALL "NotWordValue" BTY
                      (MOP FST
                           (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                        (VAR "rs" (FTY 5)))
                                  QVAR)))
                (CALL "NotWordValue" BTY
                      (MOP FST
                           (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                        (VAR "rt" (FTY 5)))
                                  QVAR))))
           (MOP SND
                (APPLY (CALL "raise'exception"
                             (ATY QTY (PTY UTY QTY))
                             (CALL "UNPREDICTABLE" (CTY "exception")
                                   (LS "DIV: NotWordValue")))
                       QVAR))
           QVAR)
      (LET
       QVAR
       (RUPD
        "LO"
        (TP (SQBKT QVAR
                   (MOP (SE F64)
                        (BOP QUOT
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32))))))
       (TP
        (SQBKT
         LU
         (RUPD
          "HLStatus"
          (TP
           (SQBKT
            (RUPD
             "HI"
             (TP
              (SQBKT
                   QVAR
                   (MOP (SE F64)
                        (BOP REM
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32))))))
            (LC "HLarith" (CTY "HLStatus"))))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DIVU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (EQ (MOP FST
                   (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                (VAR "rt" (FTY 5)))
                          QVAR))
              (LW 0 64))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "DIVU: divide by zero")))
                      QVAR))
          QVAR)
     (LET
      QVAR
      (ITE (BOP OR
                (CALL "NotWordValue" BTY
                      (MOP FST
                           (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                        (VAR "rs" (FTY 5)))
                                  QVAR)))
                (CALL "NotWordValue" BTY
                      (MOP FST
                           (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                        (VAR "rt" (FTY 5)))
                                  QVAR))))
           (MOP SND
                (APPLY (CALL "raise'exception"
                             (ATY QTY (PTY UTY QTY))
                             (CALL "UNPREDICTABLE" (CTY "exception")
                                   (LS "DIVU: NotWordValue")))
                       QVAR))
           QVAR)
      (TP
       (SQBKT
        LU
        (RUPD
         "HLStatus"
         (TP
          (SQBKT
           (RUPD
            "HI"
            (TP
             (SQBKT
              (RUPD
               "LO"
               (TP
                (SQBKT
                   QVAR
                   (MOP (SE F64)
                        (BOP DIV
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32))))))
              (MOP (SE F64)
                   (BOP MOD
                        (EX (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rs" (FTY 5)))
                                        QVAR))
                            (LN 31)
                            (LN 0)
                            F32)
                        (EX (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rt" (FTY 5)))
                                        QVAR))
                            (LN 31)
                            (LN 0)
                            F32))))))
           (LC "HLarith" (CTY "HLStatus")))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DDIV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (EQ (MOP FST
                   (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                (VAR "rt" (FTY 5)))
                          QVAR))
              (LW 0 64))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "DDIV: divide by zero")))
                      QVAR))
          QVAR)
     (LET
      QVAR
      (RUPD "LO"
            (TP (SQBKT QVAR
                       (BOP QUOT
                            (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rs" (FTY 5)))
                                        QVAR))
                            (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rt" (FTY 5)))
                                        QVAR))))))
      (TP
       (SQBKT
        LU
        (RUPD
         "HLStatus"
         (TP
          (SQBKT
           (RUPD "HI"
                 (TP (SQBKT QVAR
                            (BOP REM
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))))
           (LC "HLarith" (CTY "HLStatus")))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DDIVU"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (EQ (MOP FST
                   (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                (VAR "rt" (FTY 5)))
                          QVAR))
              (LW 0 64))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "DDIVU: divide by zero")))
                      QVAR))
          QVAR)
     (LET
      QVAR
      (RUPD "LO"
            (TP (SQBKT QVAR
                       (BOP DIV
                            (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rs" (FTY 5)))
                                        QVAR))
                            (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rt" (FTY 5)))
                                        QVAR))))))
      (TP
       (SQBKT
        LU
        (RUPD
         "HLStatus"
         (TP
          (SQBKT
           (RUPD "HI"
                 (TP (SQBKT QVAR
                            (BOP MOD
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))))))
           (LC "HLarith" (CTY "HLStatus")))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
     "dfn'MFHI" (VAR "rd" (FTY 5))
     (CLOSE QVAR
            (LET QVAR
                 (ITE (EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                          (LC "HLmtlo" (CTY "HLStatus")))
                      (MOP SND
                           (APPLY (CALL "raise'exception"
                                        (ATY QTY (PTY UTY QTY))
                                        (CALL "UNPREDICTABLE" (CTY "exception")
                                              (LS "MFHI")))
                                  QVAR))
                      QVAR)
                 (LET QVAR
                      (ITE (EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                               (LC "HLarith" (CTY "HLStatus")))
                           (RUPD "HLStatus"
                                 (TP (SQBKT QVAR (LC "HLok" (CTY "HLStatus")))))
                           QVAR)
                      (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                   (TP (SQBKT (DEST "HI" F64 QVAR)
                                              (VAR "rd" (FTY 5)))))
                             QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
     "dfn'MFLO" (VAR "rd" (FTY 5))
     (CLOSE QVAR
            (LET QVAR
                 (ITE (EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                          (LC "HLmthi" (CTY "HLStatus")))
                      (MOP SND
                           (APPLY (CALL "raise'exception"
                                        (ATY QTY (PTY UTY QTY))
                                        (CALL "UNPREDICTABLE" (CTY "exception")
                                              (LS "MFLO")))
                                  QVAR))
                      QVAR)
                 (LET QVAR
                      (ITE (EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                               (LC "HLarith" (CTY "HLStatus")))
                           (RUPD "HLStatus"
                                 (TP (SQBKT QVAR (LC "HLok" (CTY "HLStatus")))))
                           QVAR)
                      (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                   (TP (SQBKT (DEST "LO" F64 QVAR)
                                              (VAR "rd" (FTY 5)))))
                             QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'MTHI" (VAR "rd" (FTY 5))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITB (SQBKT ((EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                      (LC "HLarith" (CTY "HLStatus")))
                  (RUPD "HLStatus"
                        (TP (SQBKT QVAR (LC "HLmthi" (CTY "HLStatus"))))))
                 ((EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                      (LC "HLmtlo" (CTY "HLStatus")))
                  (RUPD "HLStatus"
                        (TP (SQBKT QVAR (LC "HLok" (CTY "HLStatus")))))))
          QVAR)
     (TP (SQBKT LU
                (RUPD "HI"
                      (TP (SQBKT QVAR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rd" (FTY 5)))
                                             QVAR))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'MTLO" (VAR "rd" (FTY 5))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITB (SQBKT ((EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                      (LC "HLarith" (CTY "HLStatus")))
                  (RUPD "HLStatus"
                        (TP (SQBKT QVAR (LC "HLmtlo" (CTY "HLStatus"))))))
                 ((EQ (DEST "HLStatus" (CTY "HLStatus") QVAR)
                      (LC "HLmthi" (CTY "HLStatus")))
                  (RUPD "HLStatus"
                        (TP (SQBKT QVAR (LC "HLok" (CTY "HLStatus")))))))
          QVAR)
     (TP (SQBKT LU
                (RUPD "LO"
                      (TP (SQBKT QVAR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rd" (FTY 5)))
                                             QVAR))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SLL"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
     (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (BOP LSL
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (MOP (CAST NTY) (VAR "sa" (FTY 5)))))
                   (VAR "rd" (FTY 5)))))
     QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SRL"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (CALL "NotWordValue" BTY
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rt" (FTY 5)))
                            QVAR)))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "SRL: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (BOP LSR
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (MOP (CAST NTY) (VAR "sa" (FTY 5)))))
                   (VAR "rd" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SRA"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (CALL "NotWordValue" BTY
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rt" (FTY 5)))
                            QVAR)))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "SRA: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (BOP ASR
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32)
                             (MOP (CAST NTY) (VAR "sa" (FTY 5)))))
                   (VAR "rd" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SLLV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
     (CALL
      "write'GPR" (ATY QTY (PTY UTY QTY))
      (TP
       (SQBKT (MOP (SE F64)
                   (BOP LSL
                        (EX (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rt" (FTY 5)))
                                        QVAR))
                            (LN 31)
                            (LN 0)
                            F32)
                        (MOP (CAST NTY)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 4)
                                 (LN 0)
                                 (FTY 5)))))
              (VAR "rd" (FTY 5)))))
     QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SRLV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (CALL "NotWordValue" BTY
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rt" (FTY 5)))
                            QVAR)))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "SRLV: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
       "write'GPR" (ATY QTY (PTY UTY QTY))
       (TP
         (SQBKT
              (MOP (SE F64)
                   (BOP LSR
                        (EX (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rt" (FTY 5)))
                                        QVAR))
                            (LN 31)
                            (LN 0)
                            F32)
                        (MOP (CAST NTY)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 4)
                                 (LN 0)
                                 (FTY 5)))))
              (VAR "rd" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SRAV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (LET
     QVAR
     (ITE (CALL "NotWordValue" BTY
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rt" (FTY 5)))
                            QVAR)))
          (MOP SND
               (APPLY (CALL "raise'exception"
                            (ATY QTY (PTY UTY QTY))
                            (CALL "UNPREDICTABLE" (CTY "exception")
                                  (LS "SRAV: NotWordValue")))
                      QVAR))
          QVAR)
     (APPLY
      (CALL
       "write'GPR" (ATY QTY (PTY UTY QTY))
       (TP
         (SQBKT
              (MOP (SE F64)
                   (BOP ASR
                        (EX (MOP FST
                                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                              (VAR "rt" (FTY 5)))
                                        QVAR))
                            (LN 31)
                            (LN 0)
                            F32)
                        (MOP (CAST NTY)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 4)
                                 (LN 0)
                                 (FTY 5)))))
              (VAR "rd" (FTY 5)))))
      QVAR))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSLL"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP LSL
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (MOP (CAST NTY) (VAR "sa" (FTY 5))))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSRL"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP LSR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (MOP (CAST NTY) (VAR "sa" (FTY 5))))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSRA"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP ASR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (MOP (CAST NTY) (VAR "sa" (FTY 5))))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSLLV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
     (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (BOP LSL
                        (MOP FST
                             (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                          (VAR "rt" (FTY 5)))
                                    QVAR))
                        (MOP (CAST NTY)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 5)
                                 (LN 0)
                                 (FTY 6))))
                   (VAR "rd" (FTY 5)))))
     QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSRLV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
     (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (BOP LSR
                        (MOP FST
                             (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                          (VAR "rt" (FTY 5)))
                                    QVAR))
                        (MOP (CAST NTY)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 5)
                                 (LN 0)
                                 (FTY 6))))
                   (VAR "rd" (FTY 5)))))
     QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSRAV"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY
     (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (BOP ASR
                        (MOP FST
                             (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                          (VAR "rt" (FTY 5)))
                                    QVAR))
                        (MOP (CAST NTY)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (LN 5)
                                 (LN 0)
                                 (FTY 6))))
                   (VAR "rd" (FTY 5)))))
     QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSLL32"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP LSL
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (BOP ADD (MOP (CAST NTY) (VAR "sa" (FTY 5)))
                                      (LN 32)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSRL32"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP LSR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (BOP ADD (MOP (CAST NTY) (VAR "sa" (FTY 5)))
                                      (LN 32)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DSRA32"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sa" (FTY 5))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (BOP ASR
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (BOP ADD (MOP (CAST NTY) (VAR "sa" (FTY 5)))
                                      (LN 32)))
                            (VAR "rd" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TGE"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "rt" (FTY 5))))
                (CLOSE QVAR
                       (ITE (BOP GE
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TGEU"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "rt" (FTY 5))))
                (CLOSE QVAR
                       (ITE (BOP UGE
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TLT"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "rt" (FTY 5))))
                (CLOSE QVAR
                       (ITE (BOP LT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TLTU"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "rt" (FTY 5))))
                (CLOSE QVAR
                       (ITE (BOP ULT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(DEFUN-STRUCT DFN-TEQ
              (((RS (UNSIGNED-BYTE-P 5 RS))
                (RT (UNSIGNED-BYTE-P 5 RT)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (IF (EQUAL (CAR (GPR RS ST$))
                         (CAR (GPR RT ST$)))
                  (SIGNALEXCEPTION 'TR ST$)
                  (MV (UNIT-VALUE) ST$)))

(DEFUN-STRUCT DFN-TNE
              (((RS (UNSIGNED-BYTE-P 5 RS))
                (RT (UNSIGNED-BYTE-P 5 RT)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (IF (NOT (EQUAL (CAR (GPR RS ST$))
                              (CAR (GPR RT ST$))))
                  (SIGNALEXCEPTION 'TR ST$)
                  (MV (UNIT-VALUE) ST$)))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TGEI"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "immediate" F16)))
                (CLOSE QVAR
                       (ITE (BOP GE
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TGEIU"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "immediate" F16)))
                (CLOSE QVAR
                       (ITE (BOP UGE
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TLTI"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "immediate" F16)))
                (CLOSE QVAR
                       (ITE (BOP LT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
    :ERROR (DEF "dfn'TLTIU"
                (TP (SQBKT (VAR "rs" (FTY 5))
                           (VAR "immediate" F16)))
                (CLOSE QVAR
                       (ITE (BOP ULT
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16)))
                            (APPLY (CALL "SignalException"
                                         (ATY QTY (PTY UTY QTY))
                                         (LC "Tr" (CTY "ExceptionType")))
                                   QVAR)
                            (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
     :ERROR (DEF "dfn'TEQI"
                 (TP (SQBKT (VAR "rs" (FTY 5))
                            (VAR "immediate" F16)))
                 (CLOSE QVAR
                        (ITE (EQ (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16)))
                             (APPLY (CALL "SignalException"
                                          (ATY QTY (PTY UTY QTY))
                                          (LC "Tr" (CTY "ExceptionType")))
                                    QVAR)
                             (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST :ERROR
       (DEF "dfn'TNEI"
            (TP (SQBKT (VAR "rs" (FTY 5))
                       (VAR "immediate" F16)))
            (CLOSE QVAR
                   (ITE (MOP NOT
                             (EQ (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))
                                 (MOP (SE F64) (VAR "immediate" F16))))
                        (APPLY (CALL "SignalException"
                                     (ATY QTY (PTY UTY QTY))
                                     (LC "Tr" (CTY "ExceptionType")))
                               QVAR)
                        (TP (SQBKT LU QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "loadByte"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)
              (VAR "unsigned" BTY)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "LOAD" (CTY "LorS")))))
      (LET
       (VAR "v0" (FTY 3))
       (BOP BXOR
            (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
            (BOP REP
                 (MOP FST
                      (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                             QVAR))
                 (LN 3)))
       (LET
        (VAR "membyte" F8)
        (EX
         (MOP
          FST
          (APPLY
           (CALL
            "LoadMemory" (ATY QTY (PTY F64 QTY))
            (TP
             (SQBKT
              (VAR "CCA" (FTY 3))
              (CONST "BYTE" (FTY 3))
              CC
              (SQBKT
               (EX (VAR "pAddr" F64)
                   (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                   (LN 3)
                   (FTY 61))
               (BOP
                 BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3))))
              (VAR "v" F64)
              (LC "DATA" (CTY "IorD")))))
           QVAR))
         (BOP ADD (LN 7)
              (BOP MUL (LN 8)
                   (MOP (CAST NTY) (VAR "v0" (FTY 3)))))
         (BOP MUL (LN 8)
              (MOP (CAST NTY) (VAR "v0" (FTY 3))))
         F8)
        (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                     (TP (SQBKT (ITE (VAR "unsigned" BTY)
                                     (MOP (CAST F64) (VAR "membyte" F8))
                                     (MOP (SE F64) (VAR "membyte" F8)))
                                (VAR "rt" (FTY 5)))))
               QVAR)))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "loadHalf"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)
              (VAR "unsigned" BTY)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (ITE
      (BOP BIT (VAR "v" F64) (LN 0))
      (APPLY (CALL "SignalException"
                   (ATY QTY (PTY UTY QTY))
                   (LC "AdEL" (CTY "ExceptionType")))
             QVAR)
      (LET
       (TP (SQBKT (VAR "pAddr" F64)
                  (VAR "CCA" (FTY 3))))
       (CALL "AddressTranslation" (PTY F64 (FTY 3))
             (TP (SQBKT (VAR "v" F64)
                        (LC "DATA" (CTY "IorD"))
                        (LC "LOAD" (CTY "LorS")))))
       (LET
        (VAR "v0" (FTY 3))
        (BOP
         BXOR
         (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
         (CC
           (SQBKT (BOP REP
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR))
                       (LN 2))
                  (LW 0 1))))
        (LET
         (VAR "memhalf" F16)
         (EX
          (MOP
           FST
           (APPLY
            (CALL
             "LoadMemory" (ATY QTY (PTY F64 QTY))
             (TP
              (SQBKT
               (VAR "CCA" (FTY 3))
               (CONST "HALFWORD" (FTY 3))
               CC
               (SQBKT
                (EX (VAR "pAddr" F64)
                    (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                    (LN 3)
                    (FTY 61))
                (BOP
                 BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (CC
                  (SQBKT
                   (BOP
                      REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 2))
                   (LW 0 1)))))
               (VAR "v" F64)
               (LC "DATA" (CTY "IorD")))))
            QVAR))
          (BOP ADD (LN 15)
               (BOP MUL (LN 8)
                    (MOP (CAST NTY) (VAR "v0" (FTY 3)))))
          (BOP MUL (LN 8)
               (MOP (CAST NTY) (VAR "v0" (FTY 3))))
          F16)
         (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                      (TP (SQBKT (ITE (VAR "unsigned" BTY)
                                      (MOP (CAST F64) (VAR "memhalf" F16))
                                      (MOP (SE F64) (VAR "memhalf" F16)))
                                 (VAR "rt" (FTY 5)))))
                QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "loadWord"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)
              (VAR "unsigned" BTY)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (ITE
      (MOP NOT
           (EQ (EX (VAR "v" F64) (LN 1) (LN 0) (FTY 2))
               (LW 0 2)))
      (APPLY (CALL "SignalException"
                   (ATY QTY (PTY UTY QTY))
                   (LC "AdEL" (CTY "ExceptionType")))
             QVAR)
      (LET
       (TP (SQBKT (VAR "pAddr" F64)
                  (VAR "CCA" (FTY 3))))
       (CALL "AddressTranslation" (PTY F64 (FTY 3))
             (TP (SQBKT (VAR "v" F64)
                        (LC "DATA" (CTY "IorD"))
                        (LC "LOAD" (CTY "LorS")))))
       (LET
        (VAR "v0" (FTY 3))
        (BOP
            BXOR
            (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
            (CC (SQBKT (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR))
                       (LW 0 2))))
        (LET
         (VAR "memword" F32)
         (EX
          (MOP
           FST
           (APPLY
            (CALL
             "LoadMemory" (ATY QTY (PTY F64 QTY))
             (TP
              (SQBKT
               (VAR "CCA" (FTY 3))
               (CONST "WORD" (FTY 3))
               CC
               (SQBKT
                (EX (VAR "pAddr" F64)
                    (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                    (LN 3)
                    (FTY 61))
                (BOP
                 BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (CC
                  (SQBKT
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LW 0 2)))))
               (VAR "v" F64)
               (LC "DATA" (CTY "IorD")))))
            QVAR))
          (BOP ADD (LN 31)
               (BOP MUL (LN 8)
                    (MOP (CAST NTY) (VAR "v0" (FTY 3)))))
          (BOP MUL (LN 8)
               (MOP (CAST NTY) (VAR "v0" (FTY 3))))
          F32)
         (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                      (TP (SQBKT (ITE (VAR "unsigned" BTY)
                                      (MOP (CAST F64) (VAR "memword" F32))
                                      (MOP (SE F64) (VAR "memword" F32)))
                                 (VAR "rt" (FTY 5)))))
                QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "loadDoubleword"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (ITE
      (MOP NOT
           (EQ (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
               (LW 0 3)))
      (APPLY (CALL "SignalException"
                   (ATY QTY (PTY UTY QTY))
                   (LC "AdEL" (CTY "ExceptionType")))
             QVAR)
      (LET
       (TP (SQBKT (VAR "pAddr" F64)
                  (VAR "CCA" (FTY 3))))
       (CALL "AddressTranslation" (PTY F64 (FTY 3))
             (TP (SQBKT (VAR "v" F64)
                        (LC "DATA" (CTY "IorD"))
                        (LC "LOAD" (CTY "LorS")))))
       (APPLY
        (CALL
            "write'GPR" (ATY QTY (PTY UTY QTY))
            (TP (SQBKT (MOP FST
                            (APPLY (CALL "LoadMemory" (ATY QTY (PTY F64 QTY))
                                         (TP (SQBKT (VAR "CCA" (FTY 3))
                                                    (CONST "DOUBLEWORD" (FTY 3))
                                                    (VAR "pAddr" F64)
                                                    (VAR "v" F64)
                                                    (LC "DATA" (CTY "IorD")))))
                                   QVAR))
                       (VAR "rt" (FTY 5)))))
        QVAR))))))))

(DEFUN-STRUCT DFN-LB
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADBYTE (TUPLE BASE RT OFFSET (FALSE))
                        ST$))

(DEFUN-STRUCT DFN-LBU
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADBYTE (TUPLE BASE RT OFFSET (TRUE))
                        ST$))

(DEFUN-STRUCT DFN-LH
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADHALF (TUPLE BASE RT OFFSET (FALSE))
                        ST$))

(DEFUN-STRUCT DFN-LHU
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADHALF (TUPLE BASE RT OFFSET (TRUE))
                        ST$))

(DEFUN-STRUCT DFN-LW
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADWORD (TUPLE BASE RT OFFSET (FALSE))
                        ST$))

(DEFUN-STRUCT DFN-LWU
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADWORD (TUPLE BASE RT OFFSET (TRUE))
                        ST$))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'LL"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
      (SQBKT
           LU
           (RUPD "LLbit"
                 (TP (SQBKT (MOP SND
                                 (APPLY (CALL "loadWord" (ATY QTY (PTY UTY QTY))
                                              (TP (SQBKT (VAR "base" (FTY 5))
                                                         (VAR "rt" (FTY 5))
                                                         (VAR "offset" F16)
                                                         LF)))
                                        QVAR))
                            (MOP SOME LT))))))))))

(DEFUN-STRUCT DFN-LD
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LOADDOUBLEWORD (TUPLE BASE RT OFFSET)
                              ST$))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'LLD"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (RUPD
           "LLbit"
           (TP (SQBKT (MOP SND
                           (APPLY (CALL "loadDoubleword" (ATY QTY (PTY UTY QTY))
                                        (TP (SQBKT (VAR "base" (FTY 5))
                                                   (VAR "rt" (FTY 5))
                                                   (VAR "offset" F16))))
                                  QVAR))
                      (MOP SOME LT))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'LWL"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "LOAD" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 2))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 1) (LN 0) (FTY 2))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 2)))
        (LET
         (VAR "v2" F64)
         (MOP
          FST
          (APPLY
           (CALL
            "LoadMemory" (ATY QTY (PTY F64 QTY))
            (TP
             (SQBKT
                 (VAR "CCA" (FTY 3))
                 CC (SQBKT (LW 0 1) (VAR "v1" (FTY 2)))
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 7 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
           QVAR))
         (LET
          (TP (SQBKT (VAR "v" F32) QVAR))
          (CS
           (TP
             (SQBKT
                  (BOP BXOR (EX (VAR "v" F64) (LN 2) (LN 2) F1)
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR)))
                  (VAR "v1" (FTY 2))))
           (SQBKT
            ((TP (SQBKT (LW 0 1) (LW 0 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 7) (LN 0) F8)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24)))
                      QVAR)))
            ((TP (SQBKT (LW 0 1) (LW 1 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 15) (LN 0) F16)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 15)
                                 (LN 0)
                                 F16))
                      QVAR)))
            ((TP (SQBKT (LW 0 1) (LW 2 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64)
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 7)
                                 (LN 0)
                                 F8))
                      QVAR)))
            ((TP (SQBKT (LW 0 1) (LW 3 2)))
             (TP (SQBKT (EX (VAR "v2" F64) (LN 31) (LN 0) F32)
                        QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 0 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 39) (LN 32) F8)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24)))
                      QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 1 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 47) (LN 32) F16)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 15)
                                 (LN 0)
                                 F16))
                      QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 2 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64)
                                 (LN 55)
                                 (LN 32)
                                 (FTY 24))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 7)
                                 (LN 0)
                                 F8))
                      QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 3 2)))
             (TP (SQBKT (EX (VAR "v2" F64) (LN 63) (LN 32) F32)
                        QVAR)))))
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (MOP (SE F64) (VAR "v" F32))
                                  (VAR "rt" (FTY 5)))))
                 QVAR)))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'LWR"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "LOAD" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 2))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 1) (LN 0) (FTY 2))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 2)))
        (LET
         (VAR "v2" F64)
         (MOP
          FST
          (APPLY
           (CALL
            "LoadMemory" (ATY QTY (PTY F64 QTY))
            (TP
             (SQBKT
                 (VAR "CCA" (FTY 3))
                 (BOP SUB (CONST "WORD" (FTY 3))
                      (CC (SQBKT (LW 0 1) (VAR "v1" (FTY 2)))))
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 7 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
           QVAR))
         (LET
          (TP (SQBKT (VAR "v" F32) QVAR))
          (CS
           (TP
             (SQBKT
                  (BOP BXOR (EX (VAR "v" F64) (LN 2) (LN 2) F1)
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR)))
                  (VAR "v1" (FTY 2))))
           (SQBKT
            ((TP (SQBKT (LW 0 1) (LW 0 2)))
             (TP (SQBKT (EX (VAR "v2" F64) (LN 31) (LN 0) F32)
                        QVAR)))
            ((TP (SQBKT (LW 0 1) (LW 1 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 24)
                                 F8)
                             (EX (VAR "v2" F64)
                                 (LN 31)
                                 (LN 8)
                                 (FTY 24)))
                      QVAR)))
            ((TP (SQBKT (LW 0 1) (LW 2 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 16)
                                 F16)
                             (EX (VAR "v2" F64) (LN 31) (LN 16) F16))
                      QVAR)))
            ((TP (SQBKT (LW 0 1) (LW 3 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 8)
                                 (FTY 24))
                             (EX (VAR "v2" F64) (LN 31) (LN 24) F8))
                      QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 0 2)))
             (TP (SQBKT (EX (VAR "v2" F64) (LN 63) (LN 32) F32)
                        QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 1 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 24)
                                 F8)
                             (EX (VAR "v2" F64)
                                 (LN 63)
                                 (LN 40)
                                 (FTY 24)))
                      QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 2 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 16)
                                 F16)
                             (EX (VAR "v2" F64) (LN 63) (LN 48) F16))
                      QVAR)))
            ((TP (SQBKT (LW 1 1) (LW 3 2)))
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 8)
                                 (FTY 24))
                             (EX (VAR "v2" F64) (LN 63) (LN 56) F8))
                      QVAR)))))
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (MOP (SE F64) (VAR "v" F32))
                                  (VAR "rt" (FTY 5)))))
                 QVAR)))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'LDL"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "LOAD" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 3))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 3)))
        (LET
         (VAR "v2" F64)
         (MOP
          FST
          (APPLY
           (CALL
            "LoadMemory" (ATY QTY (PTY F64 QTY))
            (TP
             (SQBKT
                 (VAR "CCA" (FTY 3))
                 (VAR "v1" (FTY 3))
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 7 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
           QVAR))
         (LET
          (TP (SQBKT (VAR "v" F64) QVAR))
          (CS
           (VAR "v1" (FTY 3))
           (SQBKT
            ((LW 0 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 7) (LN 0) F8)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 55)
                                 (LN 0)
                                 (FTY 56)))
                      QVAR)))
            ((LW 1 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 15) (LN 0) F16)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 47)
                                 (LN 0)
                                 (FTY 48)))
                      QVAR)))
            ((LW 2 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64)
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 39)
                                 (LN 0)
                                 (FTY 40)))
                      QVAR)))
            ((LW 3 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64) (LN 31) (LN 0) F32)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32))
                      QVAR)))
            ((LW 4 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64)
                                 (LN 39)
                                 (LN 0)
                                 (FTY 40))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24)))
                      QVAR)))
            ((LW 5 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64)
                                 (LN 47)
                                 (LN 0)
                                 (FTY 48))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 15)
                                 (LN 0)
                                 F16))
                      QVAR)))
            ((LW 6 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (VAR "v2" F64)
                                 (LN 55)
                                 (LN 0)
                                 (FTY 56))
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 7)
                                 (LN 0)
                                 F8))
                      QVAR)))
            ((LW 7 3)
             (TP (SQBKT (EX (VAR "v2" F64) (LN 63) (LN 0) F64)
                        QVAR)))))
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (VAR "v" F64)
                                  (VAR "rt" (FTY 5)))))
                 QVAR)))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'LDR"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "LOAD" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 3))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 3)))
        (LET
         (VAR "v2" F64)
         (MOP
          FST
          (APPLY
           (CALL
            "LoadMemory" (ATY QTY (PTY F64 QTY))
            (TP
             (SQBKT
                 (VAR "CCA" (FTY 3))
                 (BOP SUB (CONST "DOUBLEWORD" (FTY 3))
                      (VAR "v1" (FTY 3)))
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 7 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
           QVAR))
         (LET
          (TP (SQBKT (VAR "v" F64) QVAR))
          (CS
           (VAR "v1" (FTY 3))
           (SQBKT
            ((LW 0 3)
             (TP (SQBKT (EX (VAR "v2" F64) (LN 63) (LN 0) F64)
                        QVAR)))
            ((LW 1 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 56)
                                 F8)
                             (EX (VAR "v2" F64)
                                 (LN 63)
                                 (LN 8)
                                 (FTY 56)))
                      QVAR)))
            ((LW 2 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 48)
                                 F16)
                             (EX (VAR "v2" F64)
                                 (LN 63)
                                 (LN 16)
                                 (FTY 48)))
                      QVAR)))
            ((LW 3 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 40)
                                 (FTY 24))
                             (EX (VAR "v2" F64)
                                 (LN 63)
                                 (LN 24)
                                 (FTY 40)))
                      QVAR)))
            ((LW 4 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 32)
                                 F32)
                             (EX (VAR "v2" F64) (LN 63) (LN 32) F32))
                      QVAR)))
            ((LW 5 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 24)
                                 (FTY 40))
                             (EX (VAR "v2" F64)
                                 (LN 63)
                                 (LN 40)
                                 (FTY 24)))
                      QVAR)))
            ((LW 6 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 16)
                                 (FTY 48))
                             (EX (VAR "v2" F64) (LN 63) (LN 48) F16))
                      QVAR)))
            ((LW 7 3)
             (TP
               (SQBKT CC
                      (SQBKT (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 8)
                                 (FTY 56))
                             (EX (VAR "v2" F64) (LN 63) (LN 56) F8))
                      QVAR)))))
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (VAR "v" F64)
                                  (VAR "rt" (FTY 5)))))
                 QVAR)))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SB"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "STORE" (CTY "LorS")))))
      (APPLY
       (CALL
        "StoreMemory" (ATY QTY (PTY UTY QTY))
        (TP
         (SQBKT
          (VAR "CCA" (FTY 3))
          (CONST "BYTE" (FTY 3))
          (BOP
           LSL
           (MOP FST
                (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                             (VAR "rt" (FTY 5)))
                       QVAR))
           (BOP
            MUL (LN 8)
            (MOP
             (CAST NTY)
             (BOP BXOR
                  (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
                  (BOP REP
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR))
                       (LN 3))))))
          CC
          (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3))))
          (VAR "v" F64)
          (LC "DATA" (CTY "IorD")))))
       QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SH"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (ITE
      (BOP BIT (VAR "v" F64) (LN 0))
      (APPLY (CALL "SignalException"
                   (ATY QTY (PTY UTY QTY))
                   (LC "AdES" (CTY "ExceptionType")))
             QVAR)
      (LET
       (TP (SQBKT (VAR "pAddr" F64)
                  (VAR "CCA" (FTY 3))))
       (CALL "AddressTranslation" (PTY F64 (FTY 3))
             (TP (SQBKT (VAR "v" F64)
                        (LC "DATA" (CTY "IorD"))
                        (LC "STORE" (CTY "LorS")))))
       (APPLY
        (CALL
         "StoreMemory" (ATY QTY (PTY UTY QTY))
         (TP
          (SQBKT
           (VAR "CCA" (FTY 3))
           (CONST "HALFWORD" (FTY 3))
           (BOP
            LSL
            (MOP FST
                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                              (VAR "rt" (FTY 5)))
                        QVAR))
            (BOP
             MUL (LN 8)
             (MOP
              (CAST NTY)
              (BOP
               BXOR
               (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
               (CC
                (SQBKT
                  (BOP REP
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR))
                       (LN 2))
                  (LW 0 1)))))))
           CC
           (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP
             BXOR
             (EX (VAR "pAddr" F64)
                 (LN 2)
                 (LN 0)
                 (FTY 3))
             (CC
              (SQBKT
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 2))
                 (LW 0 1)))))
           (VAR "v" F64)
           (LC "DATA" (CTY "IorD")))))
        QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "storeWord"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (ITE
      (MOP NOT
           (EQ (EX (VAR "v" F64) (LN 1) (LN 0) (FTY 2))
               (LW 0 2)))
      (APPLY (CALL "SignalException"
                   (ATY QTY (PTY UTY QTY))
                   (LC "AdES" (CTY "ExceptionType")))
             QVAR)
      (LET
       (TP (SQBKT (VAR "pAddr" F64)
                  (VAR "CCA" (FTY 3))))
       (CALL "AddressTranslation" (PTY F64 (FTY 3))
             (TP (SQBKT (VAR "v" F64)
                        (LC "DATA" (CTY "IorD"))
                        (LC "STORE" (CTY "LorS")))))
       (APPLY
        (CALL
         "StoreMemory" (ATY QTY (PTY UTY QTY))
         (TP
          (SQBKT
           (VAR "CCA" (FTY 3))
           (CONST "WORD" (FTY 3))
           (BOP
            LSL
            (MOP FST
                 (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                              (VAR "rt" (FTY 5)))
                        QVAR))
            (BOP
             MUL (LN 8)
             (MOP
              (CAST NTY)
              (BOP
               BXOR
               (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
               (CC
                (SQBKT (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR))
                       (LW 0 2)))))))
           CC
           (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP
             BXOR
             (EX (VAR "pAddr" F64)
                 (LN 2)
                 (LN 0)
                 (FTY 3))
             (CC
               (SQBKT (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LW 0 2)))))
           (VAR "v" F64)
           (LC "DATA" (CTY "IorD")))))
        QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "storeDoubleword"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (ITE
      (MOP NOT
           (EQ (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
               (LW 0 3)))
      (APPLY (CALL "SignalException"
                   (ATY QTY (PTY UTY QTY))
                   (LC "AdES" (CTY "ExceptionType")))
             QVAR)
      (LET
         (TP (SQBKT (VAR "pAddr" F64)
                    (VAR "CCA" (FTY 3))))
         (CALL "AddressTranslation" (PTY F64 (FTY 3))
               (TP (SQBKT (VAR "v" F64)
                          (LC "DATA" (CTY "IorD"))
                          (LC "STORE" (CTY "LorS")))))
         (APPLY (CALL "StoreMemory" (ATY QTY (PTY UTY QTY))
                      (TP (SQBKT (VAR "CCA" (FTY 3))
                                 (CONST "DOUBLEWORD" (FTY 3))
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (VAR "pAddr" F64)
                                 (VAR "v" F64)
                                 (LC "DATA" (CTY "IorD")))))
                QVAR))))))))

(DEFUN-STRUCT DFN-SW
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (STOREWORD (TUPLE BASE RT OFFSET) ST$))

(DEFUN-STRUCT DFN-SD
              (((BASE (UNSIGNED-BYTE-P 5 BASE))
                (RT (UNSIGNED-BYTE-P 5 RT))
                (OFFSET (UNSIGNED-BYTE-P 16 OFFSET)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (STOREDOUBLEWORD (TUPLE BASE RT OFFSET)
                               ST$))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SC"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
        QVAR
        (CS (DEST "LLbit" (OTY BTY) QVAR)
            (SQBKT ((LO BTY)
                    (APPLY (CALL "raise'exception"
                                 (ATY QTY (PTY UTY QTY))
                                 (CALL "UNPREDICTABLE" (CTY "exception")
                                       (LS "SC: LLbit not set")))
                           QVAR))
                   ((MOP SOME LF)
                    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                 (TP (SQBKT (LW 0 64) (VAR "rt" (FTY 5)))))
                           QVAR))
                   ((MOP SOME LT)
                    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                 (TP (SQBKT (LW 1 64) (VAR "rt" (FTY 5)))))
                           (MOP SND
                                (APPLY (CALL "storeWord" (ATY QTY (PTY UTY QTY))
                                             (TP (SQBKT (VAR "base" (FTY 5))
                                                        (VAR "rt" (FTY 5))
                                                        (VAR "offset" F16))))
                                       QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
    "dfn'SCD"
    (TP (SQBKT (VAR "base" (FTY 5))
               (VAR "rt" (FTY 5))
               (VAR "offset" F16)))
    (CLOSE QVAR
           (CS (DEST "LLbit" (OTY BTY) QVAR)
               (SQBKT ((LO BTY)
                       (APPLY (CALL "raise'exception"
                                    (ATY QTY (PTY UTY QTY))
                                    (CALL "UNPREDICTABLE" (CTY "exception")
                                          (LS "SCD: LLbit not set")))
                              QVAR))
                      ((MOP SOME LF)
                       (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                    (TP (SQBKT (LW 0 64) (VAR "rt" (FTY 5)))))
                              QVAR))
                      ((MOP SOME LT)
                       (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                                    (TP (SQBKT (LW 1 64) (VAR "rt" (FTY 5)))))
                              (MOP SND
                                   (APPLY (CALL "storeDoubleword"
                                                (ATY QTY (PTY UTY QTY))
                                                (TP (SQBKT (VAR "base" (FTY 5))
                                                           (VAR "rt" (FTY 5))
                                                           (VAR "offset" F16))))
                                          QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SWL"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "STORE" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 2))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 1) (LN 0) (FTY 2))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 2)))
        (LET
         (TP (SQBKT (VAR "v2" F64) QVAR))
         (CS
          (VAR "v1" (FTY 2))
          (SQBKT
            ((LW 0 2)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 24)
                                 F8))
                        QVAR)))
            ((LW 1 2)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 16)
                                 F16))
                        QVAR)))
            ((LW 2 2)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 8)
                                 (FTY 24)))
                        QVAR)))
            ((LW 3 2)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32))
                        QVAR)))))
         (APPLY
          (CALL
           "StoreMemory" (ATY QTY (PTY UTY QTY))
           (TP
            (SQBKT
             (VAR "CCA" (FTY 3))
             (MOP (CAST (FTY 3)) (VAR "v1" (FTY 2)))
             (ITE
              (EQ (BOP BXOR (EX (VAR "v" F64) (LN 2) (LN 2) F1)
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR)))
                  (LW 1 1))
              (BOP LSL (VAR "v2" F64) (LN 32))
              (VAR "v2" F64))
             (ITE (MOP FST
                       (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                              QVAR))
                  (VAR "v0" F64)
                  (BOP BAND (VAR "v0" F64)
                       (MOP BNOT (LW 3 64))))
             (VAR "v" F64)
             (LC "DATA" (CTY "IorD")))))
          QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SWR"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "STORE" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 2))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 1) (LN 0) (FTY 2))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 2)))
        (LET
         (TP (SQBKT (VAR "v2" F64) QVAR))
         (CS
          (TP
           (SQBKT (BOP BXOR (EX (VAR "v" F64) (LN 2) (LN 2) F1)
                       (MOP FST
                            (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                   QVAR)))
                  (VAR "v1" (FTY 2))))
          (SQBKT
           ((TP (SQBKT (LW 0 1) (LW 0 2)))
            (TP (SQBKT (MOP (CAST F64)
                            (EX (MOP FST
                                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                  (VAR "rt" (FTY 5)))
                                            QVAR))
                                (LN 31)
                                (LN 0)
                                F32))
                       QVAR)))
           ((TP (SQBKT (LW 0 1) (LW 1 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24)))
                        (LN 8))
                   QVAR)))
           ((TP (SQBKT (LW 0 1) (LW 2 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 15)
                                 (LN 0)
                                 F16))
                        (LN 16))
                   QVAR)))
           ((TP (SQBKT (LW 0 1) (LW 3 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 7)
                                 (LN 0)
                                 F8))
                        (LN 24))
                   QVAR)))
           ((TP (SQBKT (LW 1 1) (LW 0 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 31)
                                 (LN 0)
                                 F32))
                        (LN 32))
                   QVAR)))
           ((TP (SQBKT (LW 1 1) (LW 1 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 23)
                                 (LN 0)
                                 (FTY 24)))
                        (LN 40))
                   QVAR)))
           ((TP (SQBKT (LW 1 1) (LW 2 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 15)
                                 (LN 0)
                                 F16))
                        (LN 48))
                   QVAR)))
           ((TP (SQBKT (LW 1 1) (LW 3 2)))
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 7)
                                 (LN 0)
                                 F8))
                        (LN 56))
                   QVAR)))))
         (APPLY
          (CALL
           "StoreMemory" (ATY QTY (PTY UTY QTY))
           (TP
            (SQBKT
                 (VAR "CCA" (FTY 3))
                 (BOP SUB (CONST "WORD" (FTY 3))
                      (MOP (CAST (FTY 3)) (VAR "v1" (FTY 2))))
                 (VAR "v2" F64)
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 3 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
          QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SDL"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "STORE" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 3))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 3)))
        (LET
         (TP (SQBKT (VAR "v2" F64) QVAR))
         (CS
          (VAR "v1" (FTY 3))
          (SQBKT
            ((LW 0 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 56)
                                 F8))
                        QVAR)))
            ((LW 1 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 48)
                                 F16))
                        QVAR)))
            ((LW 2 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 40)
                                 (FTY 24)))
                        QVAR)))
            ((LW 3 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 32)
                                 F32))
                        QVAR)))
            ((LW 4 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 24)
                                 (FTY 40)))
                        QVAR)))
            ((LW 5 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 16)
                                 (FTY 48)))
                        QVAR)))
            ((LW 6 3)
             (TP (SQBKT (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 8)
                                 (FTY 56)))
                        QVAR)))
            ((LW 7 3)
             (TP (SQBKT (MOP FST
                             (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                          (VAR "rt" (FTY 5)))
                                    QVAR))
                        QVAR)))))
         (APPLY
          (CALL
           "StoreMemory" (ATY QTY (PTY UTY QTY))
           (TP
            (SQBKT
                 (VAR "CCA" (FTY 3))
                 (VAR "v1" (FTY 3))
                 (VAR "v2" F64)
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 7 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
          QVAR))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'SDR"
   (TP (SQBKT (VAR "base" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     (VAR "v" F64)
     (BOP ADD (MOP (SE F64) (VAR "offset" F16))
          (MOP FST
               (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                            (VAR "base" (FTY 5)))
                      QVAR)))
     (LET
      (TP (SQBKT (VAR "pAddr" F64)
                 (VAR "CCA" (FTY 3))))
      (CALL "AddressTranslation" (PTY F64 (FTY 3))
            (TP (SQBKT (VAR "v" F64)
                       (LC "DATA" (CTY "IorD"))
                       (LC "STORE" (CTY "LorS")))))
      (LET
       (VAR "v0" F64)
       (CC
        (SQBKT
            (EX (VAR "pAddr" F64)
                (BOP SUB (CONST "PSIZE" NTY) (LN 1))
                (LN 3)
                (FTY 61))
            (BOP BXOR
                 (EX (VAR "pAddr" F64)
                     (LN 2)
                     (LN 0)
                     (FTY 3))
                 (BOP REP
                      (MOP FST
                           (APPLY (CONST "ReverseEndian" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LN 3)))))
       (LET
        (VAR "v1" (FTY 3))
        (BOP BXOR
             (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
             (BOP REP
                  (MOP FST
                       (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                              QVAR))
                  (LN 3)))
        (LET
         (TP (SQBKT (VAR "v2" F64) QVAR))
         (CS
          (VAR "v1" (FTY 3))
          (SQBKT
           ((LW 0 3)
            (TP (SQBKT (MOP FST
                            (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                         (VAR "rt" (FTY 5)))
                                   QVAR))
                       QVAR)))
           ((LW 1 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 8)
                                 (FTY 56)))
                        (LN 8))
                   QVAR)))
           ((LW 2 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 16)
                                 (FTY 48)))
                        (LN 16))
                   QVAR)))
           ((LW 3 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 24)
                                 (FTY 40)))
                        (LN 24))
                   QVAR)))
           ((LW 4 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 32)
                                 F32))
                        (LN 32))
                   QVAR)))
           ((LW 5 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 40)
                                 (FTY 24)))
                        (LN 40))
                   QVAR)))
           ((LW 6 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 48)
                                 F16))
                        (LN 48))
                   QVAR)))
           ((LW 7 3)
            (TP
              (SQBKT
                   (BOP LSL
                        (MOP (CAST F64)
                             (EX (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 (LN 63)
                                 (LN 56)
                                 F8))
                        (LN 56))
                   QVAR)))))
         (APPLY
          (CALL
           "StoreMemory" (ATY QTY (PTY UTY QTY))
           (TP
            (SQBKT
                 (VAR "CCA" (FTY 3))
                 (BOP SUB (CONST "DOUBLEWORD" (FTY 3))
                      (VAR "v1" (FTY 3)))
                 (VAR "v2" F64)
                 (ITE (MOP FST
                           (APPLY (CONST "BigEndianMem" (ATY QTY (PTY BTY QTY)))
                                  QVAR))
                      (VAR "v0" F64)
                      (BOP BAND (VAR "v0" F64)
                           (MOP BNOT (LW 7 64))))
                 (VAR "v" F64)
                 (LC "DATA" (CTY "IorD")))))
          QVAR))))))))))

(DEFUN-STRUCT DFN-SYNC
              ((STYPE (UNSIGNED-BYTE-P 5 STYPE)))
              (UNIT-VALUE))

(DEFUN-STRUCT DFN-BREAK (ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (SIGNALEXCEPTION 'BP ST$))

(DEFUN-STRUCT DFN-SYSCALL (ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (SIGNALEXCEPTION 'SYS ST$))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'ERET" QVAR
   (TP
    (SQBKT
     LU
     (RUPD
      "LLbit"
      (TP
       (SQBKT
        (ITE
         (DEST "ERL" BTY
               (DEST "Status" (CTY "StatusRegister")
                     (DEST "CP0" (CTY "CP0") QVAR)))
         (LET
          QVAR
          (RUPD "PC"
                (TP (SQBKT QVAR
                           (DEST "ErrorEPC"
                                 F64 (DEST "CP0" (CTY "CP0") QVAR)))))
          (LET
           (VAR "v" (CTY "CP0"))
           (DEST "CP0" (CTY "CP0") QVAR)
           (RUPD
            "CP0"
            (TP
             (SQBKT
              QVAR
              (RUPD
               "Status"
               (TP (SQBKT (VAR "v" (CTY "CP0"))
                          (RUPD "ERL"
                                (TP (SQBKT (DEST "Status" (CTY "StatusRegister")
                                                 (VAR "v" (CTY "CP0")))
                                           LF)))))))))))
         (LET
          QVAR
          (RUPD "PC"
                (TP (SQBKT QVAR
                           (DEST "EPC"
                                 F64 (DEST "CP0" (CTY "CP0") QVAR)))))
          (LET
           (VAR "v" (CTY "CP0"))
           (DEST "CP0" (CTY "CP0") QVAR)
           (RUPD
            "CP0"
            (TP
             (SQBKT
              QVAR
              (RUPD
               "Status"
               (TP (SQBKT (VAR "v" (CTY "CP0"))
                          (RUPD "EXL"
                                (TP (SQBKT (DEST "Status" (CTY "StatusRegister")
                                                 (VAR "v" (CTY "CP0")))
                                           LF))))))))))))
        (MOP SOME LF)))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
    "dfn'MTC0"
    (TP (SQBKT (VAR "rt" (FTY 5))
               (VAR "rd" (FTY 5))
               (VAR "sel" (FTY 3))))
    (CLOSE
         QVAR
         (APPLY (CALL "write'CPR" (ATY QTY (PTY UTY QTY))
                      (TP (SQBKT (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 LN 0 (VAR "rd" (FTY 5))
                                 (VAR "sel" (FTY 3)))))
                QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
    "dfn'DMTC0"
    (TP (SQBKT (VAR "rt" (FTY 5))
               (VAR "rd" (FTY 5))
               (VAR "sel" (FTY 3))))
    (CLOSE
         QVAR
         (APPLY (CALL "write'CPR" (ATY QTY (PTY UTY QTY))
                      (TP (SQBKT (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rt" (FTY 5)))
                                             QVAR))
                                 LN 0 (VAR "rd" (FTY 5))
                                 (VAR "sel" (FTY 3)))))
                QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'MFC0"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sel" (FTY 3))))
   (CLOSE
    QVAR
    (APPLY
     (CALL
        "write'GPR" (ATY QTY (PTY UTY QTY))
        (TP (SQBKT (MOP (SE F64)
                        (EX (MOP FST
                                 (APPLY (CALL "CPR" (ATY QTY (PTY F64 QTY))
                                              (TP (SQBKT LN 0 (VAR "rd" (FTY 5))
                                                         (VAR "sel" (FTY 3)))))
                                        QVAR))
                            (LN 32)
                            (LN 0)
                            (FTY 33)))
                   (VAR "rt" (FTY 5)))))
     QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'DMFC0"
   (TP (SQBKT (VAR "rt" (FTY 5))
              (VAR "rd" (FTY 5))
              (VAR "sel" (FTY 3))))
   (CLOSE
    QVAR
    (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                 (TP (SQBKT (MOP FST
                                 (APPLY (CALL "CPR" (ATY QTY (PTY F64 QTY))
                                              (TP (SQBKT LN 0 (VAR "rd" (FTY 5))
                                                         (VAR "sel" (FTY 3)))))
                                        QVAR))
                            (VAR "rt" (FTY 5)))))
           QVAR)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'J" (VAR "instr_index" (FTY 26))
   (CLOSE
        QVAR
        (TP (SQBKT LU
                   (RUPD "BranchStatus"
                         (TP (SQBKT QVAR
                                    (MOP SOME
                                         (CC (SQBKT (EX (DEST "PC" F64 QVAR)
                                                        (LN 63)
                                                        (LN 28)
                                                        (FTY 36))
                                                    (VAR "instr_index" (FTY 26))
                                                    (LW 0 2)))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'JAL" (VAR "instr_index" (FTY 26))
   (CLOSE
    QVAR
    (LET
        QVAR
        (MOP SND
             (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                          (TP (SQBKT (BOP ADD (DEST "PC" F64 QVAR) (LW 8 64))
                                     (LW 31 5))))
                    QVAR))
        (TP (SQBKT LU
                   (RUPD "BranchStatus"
                         (TP (SQBKT QVAR
                                    (MOP SOME
                                         (CC (SQBKT (EX (DEST "PC" F64 QVAR)
                                                        (LN 63)
                                                        (LN 28)
                                                        (FTY 36))
                                                    (VAR "instr_index" (FTY 26))
                                                    (LW 0 2))))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'JR" (VAR "rs" (FTY 5))
   (CLOSE
    QVAR
    (TP
      (SQBKT
           LU
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (MOP FST
                                      (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                                   (VAR "rs" (FTY 5)))
                                             QVAR))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'JALR"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rd" (FTY 5))))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (RUPD
       "BranchStatus"
       (TP
        (SQBKT
           (MOP SND
                (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                             (TP (SQBKT (BOP ADD (DEST "PC" F64 QVAR) (LW 8 64))
                                        (VAR "rd" (FTY 5)))))
                       QVAR))
           (MOP SOME
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BEQ"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (EQ (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rs" (FTY 5)))
                           QVAR))
               (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rt" (FTY 5)))
                           QVAR)))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BNE"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (MOP NOT
                (EQ (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rs" (FTY 5)))
                                QVAR))
                    (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rt" (FTY 5)))
                                QVAR))))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BLEZ"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP LE
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BGTZ"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP GT
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BLTZ"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP LT
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BGEZ"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP GE
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR)))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BLTZAL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     QVAR
     (MOP SND
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (BOP ADD (DEST "PC" F64 QVAR) (LW 8 64))
                                  (LW 31 5))))
                 QVAR))
     (TP
      (SQBKT
       LU
       (ITE
           (BOP LT
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BGEZAL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     QVAR
     (MOP SND
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (BOP ADD (DEST "PC" F64 QVAR) (LW 8 64))
                                  (LW 31 5))))
                 QVAR))
     (TP
      (SQBKT
       LU
       (ITE
           (BOP GE
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BEQL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (EQ (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rs" (FTY 5)))
                           QVAR))
               (MOP FST
                    (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                 (VAR "rt" (FTY 5)))
                           QVAR)))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BNEL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "rt" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (MOP NOT
                (EQ (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rs" (FTY 5)))
                                QVAR))
                    (MOP FST
                         (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                      (VAR "rt" (FTY 5)))
                                QVAR))))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BLEZL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP LE
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BGTZL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP GT
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BLTZL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP LT
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BGEZL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (TP
     (SQBKT
      LU
      (ITE (BOP GE
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BLTZALL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     QVAR
     (MOP SND
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (BOP ADD (DEST "PC" F64 QVAR) (LW 8 64))
                                  (LW 31 5))))
                 QVAR))
     (TP
      (SQBKT
       LU
       (ITE
           (BOP LT
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64)))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "dfn'BGEZALL"
   (TP (SQBKT (VAR "rs" (FTY 5))
              (VAR "offset" F16)))
   (CLOSE
    QVAR
    (LET
     QVAR
     (MOP SND
          (APPLY (CALL "write'GPR" (ATY QTY (PTY UTY QTY))
                       (TP (SQBKT (BOP ADD (DEST "PC" F64 QVAR) (LW 8 64))
                                  (LW 31 5))))
                 QVAR))
     (TP
      (SQBKT
       LU
       (ITE
           (BOP GE
                (MOP FST
                     (APPLY (CALL "GPR" (ATY QTY (PTY F64 QTY))
                                  (VAR "rs" (FTY 5)))
                            QVAR))
                (LW 0 64))
           (RUPD "BranchStatus"
                 (TP (SQBKT QVAR
                            (MOP SOME
                                 (BOP ADD (DEST "PC" F64 QVAR)
                                      (BOP LSL (MOP (SE F64) (VAR "offset" F16))
                                           (LN 2)))))))
           (RUPD "PC"
                 (TP (SQBKT QVAR
                            (BOP ADD (DEST "PC" F64 QVAR)
                                 (LW 4 64)))))))))))))

(DEFUN-STRUCT DFN-RESERVEDINSTRUCTION (ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (SIGNALEXCEPTION 'RI ST$))

(DEFUN-STRUCT RUN ((V0 (TYPE-INSTRUCTION V0)) ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (CASE-MATCH+ V0 ('BREAK (DFN-BREAK ST$))
                           ('ERET (DFN-ERET ST$))
                           ('RESERVEDINSTRUCTION
                            (DFN-RESERVEDINSTRUCTION ST$))
                           ('SYSCALL (DFN-SYSCALL ST$))
                           (('SYNC V120) (MV (DFN-SYNC V120) ST$))
                           (('ARITHI V1)
                            (CASE-MATCH+ V1 (('ADDI V2) (DFN-ADDI V2 ST$))
                                         (('ADDIU V3) (DFN-ADDIU V3 ST$))
                                         (('ANDI V4) (DFN-ANDI V4 ST$))
                                         (('DADDI V5) (DFN-DADDI V5 ST$))
                                         (('DADDIU V6) (DFN-DADDIU V6 ST$))
                                         (('LUI V7) (DFN-LUI V7 ST$))
                                         (('ORI V8) (DFN-ORI V8 ST$))
                                         (('SLTI V9) (DFN-SLTI V9 ST$))
                                         (('SLTIU V10) (DFN-SLTIU V10 ST$))
                                         (('XORI V11) (DFN-XORI V11 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('ARITHR V12)
                            (CASE-MATCH+ V12 (('ADD V13) (DFN-ADD V13 ST$))
                                         (('ADDU V14) (DFN-ADDU V14 ST$))
                                         (('AND V15) (DFN-AND V15 ST$))
                                         (('DADD V16) (DFN-DADD V16 ST$))
                                         (('DADDU V17) (DFN-DADDU V17 ST$))
                                         (('DSUB V18) (DFN-DSUB V18 ST$))
                                         (('DSUBU V19) (DFN-DSUBU V19 ST$))
                                         (('NOR V20) (DFN-NOR V20 ST$))
                                         (('OR V21) (DFN-OR V21 ST$))
                                         (('SLT V22) (DFN-SLT V22 ST$))
                                         (('SLTU V23) (DFN-SLTU V23 ST$))
                                         (('SUB V24) (DFN-SUB V24 ST$))
                                         (('SUBU V25) (DFN-SUBU V25 ST$))
                                         (('XOR V26) (DFN-XOR V26 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('BRANCH V27)
                            (CASE-MATCH+ V27 (('BEQ V28) (DFN-BEQ V28 ST$))
                                         (('BEQL V29) (DFN-BEQL V29 ST$))
                                         (('BGEZ V30) (DFN-BGEZ V30 ST$))
                                         (('BGEZAL V31) (DFN-BGEZAL V31 ST$))
                                         (('BGEZALL V32) (DFN-BGEZALL V32 ST$))
                                         (('BGEZL V33) (DFN-BGEZL V33 ST$))
                                         (('BGTZ V34) (DFN-BGTZ V34 ST$))
                                         (('BGTZL V35) (DFN-BGTZL V35 ST$))
                                         (('BLEZ V36) (DFN-BLEZ V36 ST$))
                                         (('BLEZL V37) (DFN-BLEZL V37 ST$))
                                         (('BLTZ V38) (DFN-BLTZ V38 ST$))
                                         (('BLTZAL V39) (DFN-BLTZAL V39 ST$))
                                         (('BLTZALL V40) (DFN-BLTZALL V40 ST$))
                                         (('BLTZL V41) (DFN-BLTZL V41 ST$))
                                         (('BNE V42) (DFN-BNE V42 ST$))
                                         (('BNEL V43) (DFN-BNEL V43 ST$))
                                         (('J V44) (DFN-J V44 ST$))
                                         (('JAL V45) (DFN-JAL V45 ST$))
                                         (('JALR V46) (DFN-JALR V46 ST$))
                                         (('JR V47) (DFN-JR V47 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('CP V48)
                            (CASE-MATCH+ V48 (('DMFC0 V49) (DFN-DMFC0 V49 ST$))
                                         (('DMTC0 V50) (DFN-DMTC0 V50 ST$))
                                         (('MFC0 V51) (DFN-MFC0 V51 ST$))
                                         (('MTC0 V52) (DFN-MTC0 V52 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('LOAD V53)
                            (CASE-MATCH+ V53 (('LB V54) (DFN-LB V54 ST$))
                                         (('LBU V55) (DFN-LBU V55 ST$))
                                         (('LD V56) (DFN-LD V56 ST$))
                                         (('LDL V57) (DFN-LDL V57 ST$))
                                         (('LDR V58) (DFN-LDR V58 ST$))
                                         (('LH V59) (DFN-LH V59 ST$))
                                         (('LHU V60) (DFN-LHU V60 ST$))
                                         (('LL V61) (DFN-LL V61 ST$))
                                         (('LLD V62) (DFN-LLD V62 ST$))
                                         (('LW V63) (DFN-LW V63 ST$))
                                         (('LWL V64) (DFN-LWL V64 ST$))
                                         (('LWR V65) (DFN-LWR V65 ST$))
                                         (('LWU V66) (DFN-LWU V66 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('MULTDIV V67)
                            (CASE-MATCH+ V67 (('DDIV V68) (DFN-DDIV V68 ST$))
                                         (('DDIVU V69) (DFN-DDIVU V69 ST$))
                                         (('DIV V70) (DFN-DIV V70 ST$))
                                         (('DIVU V71) (DFN-DIVU V71 ST$))
                                         (('DMULT V72) (DFN-DMULT V72 ST$))
                                         (('DMULTU V73) (DFN-DMULTU V73 ST$))
                                         (('MFHI V74) (DFN-MFHI V74 ST$))
                                         (('MFLO V75) (DFN-MFLO V75 ST$))
                                         (('MTHI V76) (DFN-MTHI V76 ST$))
                                         (('MTLO V77) (DFN-MTLO V77 ST$))
                                         (('MULT V78) (DFN-MULT V78 ST$))
                                         (('MULTU V79) (DFN-MULTU V79 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('SHIFT V80)
                            (CASE-MATCH+ V80 (('DSLL V81) (DFN-DSLL V81 ST$))
                                         (('DSLL32 V82) (DFN-DSLL32 V82 ST$))
                                         (('DSLLV V83) (DFN-DSLLV V83 ST$))
                                         (('DSRA V84) (DFN-DSRA V84 ST$))
                                         (('DSRA32 V85) (DFN-DSRA32 V85 ST$))
                                         (('DSRAV V86) (DFN-DSRAV V86 ST$))
                                         (('DSRL V87) (DFN-DSRL V87 ST$))
                                         (('DSRL32 V88) (DFN-DSRL32 V88 ST$))
                                         (('DSRLV V89) (DFN-DSRLV V89 ST$))
                                         (('SLL V90) (DFN-SLL V90 ST$))
                                         (('SLLV V91) (DFN-SLLV V91 ST$))
                                         (('SRA V92) (DFN-SRA V92 ST$))
                                         (('SRAV V93) (DFN-SRAV V93 ST$))
                                         (('SRL V94) (DFN-SRL V94 ST$))
                                         (('SRLV V95) (DFN-SRLV V95 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('STORE V96)
                            (CASE-MATCH+ V96 (('SB V97) (DFN-SB V97 ST$))
                                         (('SC V98) (DFN-SC V98 ST$))
                                         (('SCD V99) (DFN-SCD V99 ST$))
                                         (('SD V100) (DFN-SD V100 ST$))
                                         (('SDL V101) (DFN-SDL V101 ST$))
                                         (('SDR V102) (DFN-SDR V102 ST$))
                                         (('SH V103) (DFN-SH V103 ST$))
                                         (('SW V104) (DFN-SW V104 ST$))
                                         (('SWL V105) (DFN-SWL V105 ST$))
                                         (('SWR V106) (DFN-SWR V106 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (('TRAP V107)
                            (CASE-MATCH+ V107 (('TEQ V108) (DFN-TEQ V108 ST$))
                                         (('TEQI V109) (DFN-TEQI V109 ST$))
                                         (('TGE V110) (DFN-TGE V110 ST$))
                                         (('TGEI V111) (DFN-TGEI V111 ST$))
                                         (('TGEIU V112) (DFN-TGEIU V112 ST$))
                                         (('TGEU V113) (DFN-TGEU V113 ST$))
                                         (('TLT V114) (DFN-TLT V114 ST$))
                                         (('TLTI V115) (DFN-TLTI V115 ST$))
                                         (('TLTIU V116) (DFN-TLTIU V116 ST$))
                                         (('TLTU V117) (DFN-TLTU V117 ST$))
                                         (('TNE V118) (DFN-TNE V118 ST$))
                                         (('TNEI V119) (DFN-TNEI V119 ST$))
                                         (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))
                           (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "Decode" (VAR "w" F32)
   (LET
    (TP (SQBKT (VAR "b'31" BTY)
               (VAR "b'30" BTY)
               (VAR "b'29" BTY)
               (VAR "b'28" BTY)
               (VAR "b'27" BTY)
               (VAR "b'26" BTY)
               (VAR "b'25" BTY)
               (VAR "b'24" BTY)
               (VAR "b'23" BTY)
               (VAR "b'22" BTY)
               (VAR "b'21" BTY)
               (VAR "b'20" BTY)
               (VAR "b'19" BTY)
               (VAR "b'18" BTY)
               (VAR "b'17" BTY)
               (VAR "b'16" BTY)
               (VAR "b'15" BTY)
               (VAR "b'14" BTY)
               (VAR "b'13" BTY)
               (VAR "b'12" BTY)
               (VAR "b'11" BTY)
               (VAR "b'10" BTY)
               (VAR "b'9" BTY)
               (VAR "b'8" BTY)
               (VAR "b'7" BTY)
               (VAR "b'6" BTY)
               (VAR "b'5" BTY)
               (VAR "b'4" BTY)
               (VAR "b'3" BTY)
               (VAR "b'2" BTY)
               (VAR "b'1" BTY)
               (VAR "b'0" BTY)))
    (BL 32 (VAR "w" F32))
    (ITE
     (BOP AND (MOP NOT (VAR "b'31" BTY))
          (BOP AND (MOP NOT (VAR "b'29" BTY))
               (MOP NOT (VAR "b'28" BTY))))
     (ITB
      (SQBKT
       ((BOP AND (MOP NOT (VAR "b'30" BTY))
             (BOP AND (MOP NOT (VAR "b'27" BTY))
                  (MOP NOT (VAR "b'26" BTY))))
        (LET
         (VAR "rt" (FTY 5))
         (EX (VAR "w" F32)
             (LN 20)
             (LN 16)
             (FTY 5))
         (LET
          (VAR "rs" (FTY 5))
          (EX (VAR "w" F32)
              (LN 25)
              (LN 21)
              (FTY 5))
          (LET
           (VAR "rd" (FTY 5))
           (EX (VAR "w" F32)
               (LN 15)
               (LN 11)
               (FTY 5))
           (LET
            (VAR "imm5" (FTY 5))
            (EX (VAR "w" F32)
                (LN 10)
                (LN 6)
                (FTY 5))
            (LET
             (TP (SQBKT (VAR "b'5" BTY)
                        (VAR "b'4" BTY)
                        (VAR "b'3" BTY)
                        (VAR "b'2" BTY)
                        (VAR "b'1" BTY)
                        (VAR "b'0" BTY)))
             (BL 6
                 (EX (VAR "w" F32)
                     (LN 5)
                     (LN 0)
                     (FTY 6)))
             (ITB
              (SQBKT
               ((VAR "b'5" BTY)
                (ITB
                 (SQBKT
                  ((VAR "b'2" BTY)
                   (ITB
                    (SQBKT
                     ((VAR "b'3" BTY)
                      (ITB
                       (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "ArithR" (CTY "instruction")
                                     (CALL "DADD" (CTY "ArithR")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5)))))))
                              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                                         (VAR "b'0" BTY)))
                               (CALL "ArithR" (CTY "instruction")
                                     (CALL "DADDU" (CTY "ArithR")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5)))))))
                              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                    (BOP AND (VAR "b'1" BTY)
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "ArithR" (CTY "instruction")
                                     (CALL "DSUB" (CTY "ArithR")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5)))))))
                              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                    (BOP AND (VAR "b'1" BTY)
                                         (VAR "b'0" BTY)))
                               (CALL "ArithR" (CTY "instruction")
                                     (CALL "DSUBU" (CTY "ArithR")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5)))))))
                              ((BOP AND (VAR "b'4" BTY)
                                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "Shift" (CTY "instruction")
                                     (CALL "DSLL32" (CTY "Shift")
                                           (TP (SQBKT (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5))
                                                      (VAR "imm5" (FTY 5)))))))
                              ((BOP AND (VAR "b'4" BTY)
                                    (BOP AND (VAR "b'1" BTY)
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "Shift" (CTY "instruction")
                                     (CALL "DSRL32" (CTY "Shift")
                                           (TP (SQBKT (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5))
                                                      (VAR "imm5" (FTY 5)))))))
                              ((BOP AND (VAR "b'4" BTY)
                                    (BOP AND (VAR "b'1" BTY)
                                         (VAR "b'0" BTY)))
                               (CALL "Shift" (CTY "instruction")
                                     (CALL "DSRA32" (CTY "Shift")
                                           (TP (SQBKT (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5))
                                                      (VAR "imm5" (FTY 5))))))))
                       (CONST "ReservedInstruction"
                              (CTY "instruction"))))
                     ((BOP AND (MOP NOT (VAR "b'4" BTY))
                           (BOP AND (MOP NOT (VAR "b'1" BTY))
                                (MOP NOT (VAR "b'0" BTY))))
                      (CALL "ArithR" (CTY "instruction")
                            (CALL "AND" (CTY "ArithR")
                                  (TP (SQBKT (VAR "rs" (FTY 5))
                                             (VAR "rt" (FTY 5))
                                             (VAR "rd" (FTY 5)))))))
                     ((BOP AND (MOP NOT (VAR "b'4" BTY))
                           (BOP AND (MOP NOT (VAR "b'1" BTY))
                                (VAR "b'0" BTY)))
                      (CALL "ArithR" (CTY "instruction")
                            (CALL "OR" (CTY "ArithR")
                                  (TP (SQBKT (VAR "rs" (FTY 5))
                                             (VAR "rt" (FTY 5))
                                             (VAR "rd" (FTY 5)))))))
                     ((BOP AND (MOP NOT (VAR "b'4" BTY))
                           (BOP AND (VAR "b'1" BTY)
                                (MOP NOT (VAR "b'0" BTY))))
                      (CALL "ArithR" (CTY "instruction")
                            (CALL "XOR" (CTY "ArithR")
                                  (TP (SQBKT (VAR "rs" (FTY 5))
                                             (VAR "rt" (FTY 5))
                                             (VAR "rd" (FTY 5)))))))
                     ((BOP AND (MOP NOT (VAR "b'4" BTY))
                           (BOP AND (VAR "b'1" BTY)
                                (VAR "b'0" BTY)))
                      (CALL "ArithR" (CTY "instruction")
                            (CALL "NOR" (CTY "ArithR")
                                  (TP (SQBKT (VAR "rs" (FTY 5))
                                             (VAR "rt" (FTY 5))
                                             (VAR "rd" (FTY 5)))))))
                     ((BOP AND (VAR "b'4" BTY)
                           (BOP AND (MOP NOT (VAR "b'1" BTY))
                                (MOP NOT (VAR "b'0" BTY))))
                      (CALL "Trap" (CTY "instruction")
                            (CALL "TEQ" (CTY "Trap")
                                  (TP (SQBKT (VAR "rs" (FTY 5))
                                             (VAR "rt" (FTY 5)))))))
                     ((BOP AND (VAR "b'4" BTY)
                           (BOP AND (VAR "b'1" BTY)
                                (MOP NOT (VAR "b'0" BTY))))
                      (CALL "Trap" (CTY "instruction")
                            (CALL "TNE" (CTY "Trap")
                                  (TP (SQBKT (VAR "rs" (FTY 5))
                                             (VAR "rt" (FTY 5))))))))
                    (CONST "ReservedInstruction"
                           (CTY "instruction"))))
                  ((VAR "b'4" BTY)
                   (ITB
                       (SQBKT ((BOP AND (MOP NOT (VAR "b'3" BTY))
                                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "Trap" (CTY "instruction")
                                     (CALL "TGE" (CTY "Trap")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5)))))))
                              ((BOP AND (MOP NOT (VAR "b'3" BTY))
                                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                                         (VAR "b'0" BTY)))
                               (CALL "Trap" (CTY "instruction")
                                     (CALL "TGEU" (CTY "Trap")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5)))))))
                              ((BOP AND (MOP NOT (VAR "b'3" BTY))
                                    (BOP AND (VAR "b'1" BTY)
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "Trap" (CTY "instruction")
                                     (CALL "TLT" (CTY "Trap")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5)))))))
                              ((BOP AND (MOP NOT (VAR "b'3" BTY))
                                    (BOP AND (VAR "b'1" BTY)
                                         (VAR "b'0" BTY)))
                               (CALL "Trap" (CTY "instruction")
                                     (CALL "TLTU" (CTY "Trap")
                                           (TP (SQBKT (VAR "rs" (FTY 5))
                                                      (VAR "rt" (FTY 5)))))))
                              ((BOP AND (VAR "b'3" BTY)
                                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "Shift" (CTY "instruction")
                                     (CALL "DSLL" (CTY "Shift")
                                           (TP (SQBKT (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5))
                                                      (VAR "imm5" (FTY 5)))))))
                              ((BOP AND (VAR "b'3" BTY)
                                    (BOP AND (VAR "b'1" BTY)
                                         (MOP NOT (VAR "b'0" BTY))))
                               (CALL "Shift" (CTY "instruction")
                                     (CALL "DSRL" (CTY "Shift")
                                           (TP (SQBKT (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5))
                                                      (VAR "imm5" (FTY 5)))))))
                              ((BOP AND (VAR "b'3" BTY)
                                    (BOP AND (VAR "b'1" BTY)
                                         (VAR "b'0" BTY)))
                               (CALL "Shift" (CTY "instruction")
                                     (CALL "DSRA" (CTY "Shift")
                                           (TP (SQBKT (VAR "rt" (FTY 5))
                                                      (VAR "rd" (FTY 5))
                                                      (VAR "imm5" (FTY 5))))))))
                       (CONST "ReservedInstruction"
                              (CTY "instruction"))))
                  ((BOP AND (MOP NOT (VAR "b'3" BTY))
                        (BOP AND (MOP NOT (VAR "b'1" BTY))
                             (MOP NOT (VAR "b'0" BTY))))
                   (CALL "ArithR" (CTY "instruction")
                         (CALL "ADD" (CTY "ArithR")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "rd" (FTY 5)))))))
                  ((BOP AND (MOP NOT (VAR "b'3" BTY))
                        (BOP AND (MOP NOT (VAR "b'1" BTY))
                             (VAR "b'0" BTY)))
                   (CALL "ArithR" (CTY "instruction")
                         (CALL "ADDU" (CTY "ArithR")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "rd" (FTY 5)))))))
                  ((BOP AND (MOP NOT (VAR "b'3" BTY))
                        (BOP AND (VAR "b'1" BTY)
                             (MOP NOT (VAR "b'0" BTY))))
                   (CALL "ArithR" (CTY "instruction")
                         (CALL "SUB" (CTY "ArithR")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "rd" (FTY 5)))))))
                  ((BOP AND (MOP NOT (VAR "b'3" BTY))
                        (BOP AND (VAR "b'1" BTY)
                             (VAR "b'0" BTY)))
                   (CALL "ArithR" (CTY "instruction")
                         (CALL "SUBU" (CTY "ArithR")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "rd" (FTY 5)))))))
                  ((BOP AND (VAR "b'3" BTY)
                        (BOP AND (VAR "b'1" BTY)
                             (MOP NOT (VAR "b'0" BTY))))
                   (CALL "ArithR" (CTY "instruction")
                         (CALL "SLT" (CTY "ArithR")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "rd" (FTY 5)))))))
                  ((BOP AND (VAR "b'3" BTY)
                        (BOP AND (VAR "b'1" BTY)
                             (VAR "b'0" BTY)))
                   (CALL "ArithR" (CTY "instruction")
                         (CALL "SLTU" (CTY "ArithR")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "rd" (FTY 5))))))))
                 (CONST "ReservedInstruction"
                        (CTY "instruction"))))
               ((VAR "b'3" BTY)
                (ITB
                 (SQBKT
                   ((VAR "b'2" BTY)
                    (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                      (BOP AND (MOP NOT (VAR "b'1" BTY))
                                           (MOP NOT (VAR "b'0" BTY))))
                                 (CONST "SYSCALL" (CTY "instruction")))
                                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                      (BOP AND (MOP NOT (VAR "b'1" BTY))
                                           (VAR "b'0" BTY)))
                                 (CONST "BREAK" (CTY "instruction")))
                                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                      (BOP AND (VAR "b'1" BTY)
                                           (VAR "b'0" BTY)))
                                 (CALL "SYNC" (CTY "instruction")
                                       (VAR "imm5" (FTY 5))))
                                ((BOP AND (VAR "b'4" BTY)
                                      (BOP AND (MOP NOT (VAR "b'1" BTY))
                                           (MOP NOT (VAR "b'0" BTY))))
                                 (CALL "MultDiv" (CTY "instruction")
                                       (CALL "DMULT" (CTY "MultDiv")
                                             (TP (SQBKT (VAR "rs" (FTY 5))
                                                        (VAR "rt" (FTY 5)))))))
                                ((BOP AND (VAR "b'4" BTY)
                                      (BOP AND (MOP NOT (VAR "b'1" BTY))
                                           (VAR "b'0" BTY)))
                                 (CALL "MultDiv" (CTY "instruction")
                                       (CALL "DMULTU" (CTY "MultDiv")
                                             (TP (SQBKT (VAR "rs" (FTY 5))
                                                        (VAR "rt" (FTY 5)))))))
                                ((BOP AND (VAR "b'4" BTY)
                                      (BOP AND (VAR "b'1" BTY)
                                           (MOP NOT (VAR "b'0" BTY))))
                                 (CALL "MultDiv" (CTY "instruction")
                                       (CALL "DDIV" (CTY "MultDiv")
                                             (TP (SQBKT (VAR "rs" (FTY 5))
                                                        (VAR "rt" (FTY 5)))))))
                                ((BOP AND (VAR "b'4" BTY)
                                      (BOP AND (VAR "b'1" BTY)
                                           (VAR "b'0" BTY)))
                                 (CALL "MultDiv" (CTY "instruction")
                                       (CALL "DDIVU" (CTY "MultDiv")
                                             (TP (SQBKT (VAR "rs" (FTY 5))
                                                        (VAR "rt" (FTY 5))))))))
                         (CONST "ReservedInstruction"
                                (CTY "instruction"))))
                   ((BOP AND (MOP NOT (VAR "b'4" BTY))
                         (BOP AND (MOP NOT (VAR "b'1" BTY))
                              (MOP NOT (VAR "b'0" BTY))))
                    (CALL "Branch" (CTY "instruction")
                          (CALL "JR" (CTY "Branch")
                                (VAR "rs" (FTY 5)))))
                   ((BOP AND (MOP NOT (VAR "b'4" BTY))
                         (BOP AND (MOP NOT (VAR "b'1" BTY))
                              (VAR "b'0" BTY)))
                    (CALL "Branch" (CTY "instruction")
                          (CALL "JALR" (CTY "Branch")
                                (TP (SQBKT (VAR "rs" (FTY 5))
                                           (VAR "rd" (FTY 5)))))))
                   ((BOP AND (VAR "b'4" BTY)
                         (BOP AND (MOP NOT (VAR "b'1" BTY))
                              (MOP NOT (VAR "b'0" BTY))))
                    (CALL "MultDiv" (CTY "instruction")
                          (CALL "MULT" (CTY "MultDiv")
                                (TP (SQBKT (VAR "rs" (FTY 5))
                                           (VAR "rt" (FTY 5)))))))
                   ((BOP AND (VAR "b'4" BTY)
                         (BOP AND (MOP NOT (VAR "b'1" BTY))
                              (VAR "b'0" BTY)))
                    (CALL "MultDiv" (CTY "instruction")
                          (CALL "MULTU" (CTY "MultDiv")
                                (TP (SQBKT (VAR "rs" (FTY 5))
                                           (VAR "rt" (FTY 5)))))))
                   ((BOP AND (VAR "b'4" BTY)
                         (BOP AND (VAR "b'1" BTY)
                              (MOP NOT (VAR "b'0" BTY))))
                    (CALL "MultDiv" (CTY "instruction")
                          (CALL "DIV" (CTY "MultDiv")
                                (TP (SQBKT (VAR "rs" (FTY 5))
                                           (VAR "rt" (FTY 5)))))))
                   ((BOP AND (VAR "b'4" BTY)
                         (BOP AND (VAR "b'1" BTY)
                              (VAR "b'0" BTY)))
                    (CALL "MultDiv" (CTY "instruction")
                          (CALL "DIVU" (CTY "MultDiv")
                                (TP (SQBKT (VAR "rs" (FTY 5))
                                           (VAR "rt" (FTY 5))))))))
                 (CONST "ReservedInstruction"
                        (CTY "instruction"))))
               ((VAR "b'4" BTY)
                (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'2" BTY))
                                  (BOP AND (MOP NOT (VAR "b'1" BTY))
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "MultDiv" (CTY "instruction")
                                   (CALL "MFHI" (CTY "MultDiv")
                                         (VAR "rd" (FTY 5)))))
                            ((BOP AND (MOP NOT (VAR "b'2" BTY))
                                  (BOP AND (MOP NOT (VAR "b'1" BTY))
                                       (VAR "b'0" BTY)))
                             (CALL "MultDiv" (CTY "instruction")
                                   (CALL "MTHI" (CTY "MultDiv")
                                         (VAR "rd" (FTY 5)))))
                            ((BOP AND (MOP NOT (VAR "b'2" BTY))
                                  (BOP AND (VAR "b'1" BTY)
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "MultDiv" (CTY "instruction")
                                   (CALL "MFLO" (CTY "MultDiv")
                                         (VAR "rs" (FTY 5)))))
                            ((BOP AND (MOP NOT (VAR "b'2" BTY))
                                  (BOP AND (VAR "b'1" BTY)
                                       (VAR "b'0" BTY)))
                             (CALL "MultDiv" (CTY "instruction")
                                   (CALL "MTLO" (CTY "MultDiv")
                                         (VAR "rs" (FTY 5)))))
                            ((BOP AND (VAR "b'2" BTY)
                                  (BOP AND (MOP NOT (VAR "b'1" BTY))
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "Shift" (CTY "instruction")
                                   (CALL "DSLLV" (CTY "Shift")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "rd" (FTY 5)))))))
                            ((BOP AND (VAR "b'2" BTY)
                                  (BOP AND (VAR "b'1" BTY)
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "Shift" (CTY "instruction")
                                   (CALL "DSRLV" (CTY "Shift")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "rd" (FTY 5)))))))
                            ((BOP AND (VAR "b'2" BTY)
                                  (BOP AND (VAR "b'1" BTY)
                                       (VAR "b'0" BTY)))
                             (CALL "Shift" (CTY "instruction")
                                   (CALL "DSRAV" (CTY "Shift")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "rd" (FTY 5))))))))
                     (CONST "ReservedInstruction"
                            (CTY "instruction"))))
               ((BOP AND (MOP NOT (VAR "b'2" BTY))
                     (BOP AND (MOP NOT (VAR "b'1" BTY))
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Shift" (CTY "instruction")
                      (CALL "SLL" (CTY "Shift")
                            (TP (SQBKT (VAR "rt" (FTY 5))
                                       (VAR "rd" (FTY 5))
                                       (VAR "imm5" (FTY 5)))))))
               ((BOP AND (MOP NOT (VAR "b'2" BTY))
                     (BOP AND (VAR "b'1" BTY)
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Shift" (CTY "instruction")
                      (CALL "SRL" (CTY "Shift")
                            (TP (SQBKT (VAR "rt" (FTY 5))
                                       (VAR "rd" (FTY 5))
                                       (VAR "imm5" (FTY 5)))))))
               ((BOP AND (MOP NOT (VAR "b'2" BTY))
                     (BOP AND (VAR "b'1" BTY)
                          (VAR "b'0" BTY)))
                (CALL "Shift" (CTY "instruction")
                      (CALL "SRA" (CTY "Shift")
                            (TP (SQBKT (VAR "rt" (FTY 5))
                                       (VAR "rd" (FTY 5))
                                       (VAR "imm5" (FTY 5)))))))
               ((BOP AND (VAR "b'2" BTY)
                     (BOP AND (MOP NOT (VAR "b'1" BTY))
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Shift" (CTY "instruction")
                      (CALL "SLLV" (CTY "Shift")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "rd" (FTY 5)))))))
               ((BOP AND (VAR "b'2" BTY)
                     (BOP AND (VAR "b'1" BTY)
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Shift" (CTY "instruction")
                      (CALL "SRLV" (CTY "Shift")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "rd" (FTY 5)))))))
               ((BOP AND (VAR "b'2" BTY)
                     (BOP AND (VAR "b'1" BTY)
                          (VAR "b'0" BTY)))
                (CALL "Shift" (CTY "instruction")
                      (CALL "SRAV" (CTY "Shift")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "rd" (FTY 5))))))))
              (CONST "ReservedInstruction"
                     (CTY "instruction")))))))))
       ((BOP AND (MOP NOT (VAR "b'30" BTY))
             (BOP AND (MOP NOT (VAR "b'27" BTY))
                  (VAR "b'26" BTY)))
        (LET
         (VAR "rs" (FTY 5))
         (EX (VAR "w" F32)
             (LN 25)
             (LN 21)
             (FTY 5))
         (LET
          (VAR "immediate" F16)
          (EX (VAR "w" F32) (LN 15) (LN 0) F16)
          (LET
           (TP (SQBKT (VAR "b'4" BTY)
                      (VAR "b'3" BTY)
                      (VAR "b'2" BTY)
                      (VAR "b'1" BTY)
                      (VAR "b'0" BTY)))
           (BL 5
               (EX (VAR "w" F32)
                   (LN 20)
                   (LN 16)
                   (FTY 5)))
           (ITB
            (SQBKT
                ((VAR "b'1" BTY)
                 (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (BOP AND (MOP NOT (VAR "b'2" BTY))
                                             (MOP NOT (VAR "b'0" BTY)))))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BLTZL" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (BOP AND (MOP NOT (VAR "b'2" BTY))
                                             (VAR "b'0" BTY))))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BGEZL" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (BOP AND (MOP NOT (VAR "b'2" BTY))
                                             (MOP NOT (VAR "b'0" BTY)))))
                              (CALL "Trap" (CTY "instruction")
                                    (CALL "TLTI" (CTY "Trap")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (BOP AND (MOP NOT (VAR "b'2" BTY))
                                             (VAR "b'0" BTY))))
                              (CALL "Trap" (CTY "instruction")
                                    (CALL "TLTIU" (CTY "Trap")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (BOP AND (VAR "b'2" BTY)
                                             (MOP NOT (VAR "b'0" BTY)))))
                              (CALL "Trap" (CTY "instruction")
                                    (CALL "TNEI" (CTY "Trap")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (BOP AND (MOP NOT (VAR "b'2" BTY))
                                             (MOP NOT (VAR "b'0" BTY)))))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BLTZALL" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (BOP AND (MOP NOT (VAR "b'2" BTY))
                                             (VAR "b'0" BTY))))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BGEZALL" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16)))))))
                      (CONST "ReservedInstruction"
                             (CTY "instruction"))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (BOP AND (MOP NOT (VAR "b'2" BTY))
                                (MOP NOT (VAR "b'0" BTY)))))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BLTZ" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (BOP AND (MOP NOT (VAR "b'2" BTY))
                                (VAR "b'0" BTY))))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BGEZ" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (BOP AND (MOP NOT (VAR "b'2" BTY))
                                (MOP NOT (VAR "b'0" BTY)))))
                 (CALL "Trap" (CTY "instruction")
                       (CALL "TGEI" (CTY "Trap")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (BOP AND (MOP NOT (VAR "b'2" BTY))
                                (VAR "b'0" BTY))))
                 (CALL "Trap" (CTY "instruction")
                       (CALL "TGEIU" (CTY "Trap")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (BOP AND (VAR "b'2" BTY)
                                (MOP NOT (VAR "b'0" BTY)))))
                 (CALL "Trap" (CTY "instruction")
                       (CALL "TEQI" (CTY "Trap")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (VAR "b'4" BTY)
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (BOP AND (MOP NOT (VAR "b'2" BTY))
                                (MOP NOT (VAR "b'0" BTY)))))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BLTZAL" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (VAR "b'4" BTY)
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (BOP AND (MOP NOT (VAR "b'2" BTY))
                                (VAR "b'0" BTY))))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BGEZAL" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16)))))))
            (CONST "ReservedInstruction"
                   (CTY "instruction")))))))
       ((BOP AND (MOP NOT (VAR "b'30" BTY))
             (BOP AND (VAR "b'27" BTY)
                  (MOP NOT (VAR "b'26" BTY))))
        (CALL "Branch" (CTY "instruction")
              (CALL "J" (CTY "Branch")
                    (EX (VAR "w" F32)
                        (LN 25)
                        (LN 0)
                        (FTY 26)))))
       ((BOP AND (MOP NOT (VAR "b'30" BTY))
             (BOP AND (VAR "b'27" BTY)
                  (VAR "b'26" BTY)))
        (CALL "Branch" (CTY "instruction")
              (CALL "JAL" (CTY "Branch")
                    (EX (VAR "w" F32)
                        (LN 25)
                        (LN 0)
                        (FTY 26)))))
       ((BOP
         AND (VAR "b'30" BTY)
         (BOP
          AND (MOP NOT (VAR "b'27" BTY))
          (BOP
           AND (MOP NOT (VAR "b'26" BTY))
           (BOP
               AND (MOP NOT (VAR "b'10" BTY))
               (BOP AND (MOP NOT (VAR "b'9" BTY))
                    (BOP AND (MOP NOT (VAR "b'8" BTY))
                         (BOP AND (MOP NOT (VAR "b'7" BTY))
                              (BOP AND (MOP NOT (VAR "b'6" BTY))
                                   (BOP AND (MOP NOT (VAR "b'5" BTY))
                                        (BOP AND (MOP NOT (VAR "b'4" BTY))
                                             (MOP NOT (VAR "b'3" BTY))))))))))))
        (LET
         (VAR "sel" (FTY 3))
         (EX (VAR "w" F32) (LN 2) (LN 0) (FTY 3))
         (LET
          (VAR "rt" (FTY 5))
          (EX (VAR "w" F32)
              (LN 20)
              (LN 16)
              (FTY 5))
          (LET
           (VAR "rd" (FTY 5))
           (EX (VAR "w" F32)
               (LN 15)
               (LN 11)
               (FTY 5))
           (LET
              (TP (SQBKT (VAR "b'4" BTY)
                         (VAR "b'3" BTY)
                         (VAR "b'2" BTY)
                         (VAR "b'1" BTY)
                         (VAR "b'0" BTY)))
              (BL 5
                  (EX (VAR "w" F32)
                      (LN 25)
                      (LN 21)
                      (FTY 5)))
              (ITE (BOP AND (MOP NOT (VAR "b'4" BTY))
                        (BOP AND (MOP NOT (VAR "b'3" BTY))
                             (MOP NOT (VAR "b'1" BTY))))
                   (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'2" BTY))
                                     (MOP NOT (VAR "b'0" BTY)))
                                (CALL "CP" (CTY "instruction")
                                      (CALL "MFC0" (CTY "CP")
                                            (TP (SQBKT (VAR "rt" (FTY 5))
                                                       (VAR "rd" (FTY 5))
                                                       (VAR "sel" (FTY 3)))))))
                               ((BOP AND (MOP NOT (VAR "b'2" BTY))
                                     (VAR "b'0" BTY))
                                (CALL "CP" (CTY "instruction")
                                      (CALL "DMFC0" (CTY "CP")
                                            (TP (SQBKT (VAR "rt" (FTY 5))
                                                       (VAR "rd" (FTY 5))
                                                       (VAR "sel" (FTY 3)))))))
                               ((BOP AND (VAR "b'2" BTY)
                                     (MOP NOT (VAR "b'0" BTY)))
                                (CALL "CP" (CTY "instruction")
                                      (CALL "MTC0" (CTY "CP")
                                            (TP (SQBKT (VAR "rt" (FTY 5))
                                                       (VAR "rd" (FTY 5))
                                                       (VAR "sel" (FTY 3)))))))
                               ((BOP AND (VAR "b'2" BTY)
                                     (VAR "b'0" BTY))
                                (CALL "CP" (CTY "instruction")
                                      (CALL "DMTC0" (CTY "CP")
                                            (TP (SQBKT (VAR "rt" (FTY 5))
                                                       (VAR "rd" (FTY 5))
                                                       (VAR "sel" (FTY 3))))))))
                        (CONST "ReservedInstruction"
                               (CTY "instruction")))
                   (CONST "ReservedInstruction"
                          (CTY "instruction")))))))))
      (LET
       (VAR "rt" (FTY 5))
       (EX (VAR "w" F32)
           (LN 20)
           (LN 16)
           (FTY 5))
       (LET
        (VAR "rs" (FTY 5))
        (EX (VAR "w" F32)
            (LN 25)
            (LN 21)
            (FTY 5))
        (LET
         (VAR "immediate" F16)
         (EX (VAR "w" F32) (LN 15) (LN 0) F16)
         (LET
          (TP (SQBKT (VAR "b'5" BTY)
                     (VAR "b'4" BTY)
                     (VAR "b'3" BTY)
                     (VAR "b'2" BTY)
                     (VAR "b'1" BTY)
                     (VAR "b'0" BTY)))
          (BL 6
              (EX (VAR "w" F32)
                  (LN 31)
                  (LN 26)
                  (FTY 6)))
          (ITB
           (SQBKT
            ((VAR "b'5" BTY)
             (ITB
              (SQBKT
               ((VAR "b'2" BTY)
                (ITB
                 (SQBKT
                  ((VAR "b'3" BTY)
                   (ITB
                      (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'1" BTY))
                                        (MOP NOT (VAR "b'0" BTY))))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SDL" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'1" BTY))
                                        (VAR "b'0" BTY)))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SDR" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'1" BTY)
                                        (MOP NOT (VAR "b'0" BTY))))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SWR" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (MOP NOT (VAR "b'1" BTY))
                                        (MOP NOT (VAR "b'0" BTY))))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SCD" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (VAR "b'1" BTY)
                                        (VAR "b'0" BTY)))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SD" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16)))))))
                      (CONST "ReservedInstruction"
                             (CTY "instruction"))))
                  ((BOP AND (MOP NOT (VAR "b'4" BTY))
                        (BOP AND (MOP NOT (VAR "b'1" BTY))
                             (MOP NOT (VAR "b'0" BTY))))
                   (CALL "Load" (CTY "instruction")
                         (CALL "LBU" (CTY "Load")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "immediate" F16))))))
                  ((BOP AND (MOP NOT (VAR "b'4" BTY))
                        (BOP AND (MOP NOT (VAR "b'1" BTY))
                             (VAR "b'0" BTY)))
                   (CALL "Load" (CTY "instruction")
                         (CALL "LHU" (CTY "Load")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "immediate" F16))))))
                  ((BOP AND (MOP NOT (VAR "b'4" BTY))
                        (BOP AND (VAR "b'1" BTY)
                             (MOP NOT (VAR "b'0" BTY))))
                   (CALL "Load" (CTY "instruction")
                         (CALL "LWR" (CTY "Load")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "immediate" F16))))))
                  ((BOP AND (MOP NOT (VAR "b'4" BTY))
                        (BOP AND (VAR "b'1" BTY)
                             (VAR "b'0" BTY)))
                   (CALL "Load" (CTY "instruction")
                         (CALL "LWU" (CTY "Load")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "immediate" F16))))))
                  ((BOP AND (VAR "b'4" BTY)
                        (BOP AND (MOP NOT (VAR "b'1" BTY))
                             (MOP NOT (VAR "b'0" BTY))))
                   (CALL "Load" (CTY "instruction")
                         (CALL "LLD" (CTY "Load")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "immediate" F16))))))
                  ((BOP AND (VAR "b'4" BTY)
                        (BOP AND (VAR "b'1" BTY)
                             (VAR "b'0" BTY)))
                   (CALL "Load" (CTY "instruction")
                         (CALL "LD" (CTY "Load")
                               (TP (SQBKT (VAR "rs" (FTY 5))
                                          (VAR "rt" (FTY 5))
                                          (VAR "immediate" F16)))))))
                 (CONST "ReservedInstruction"
                        (CTY "instruction"))))
               ((VAR "b'3" BTY)
                (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                  (BOP AND (MOP NOT (VAR "b'1" BTY))
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "Store" (CTY "instruction")
                                   (CALL "SB" (CTY "Store")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "immediate" F16))))))
                            ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                  (BOP AND (MOP NOT (VAR "b'1" BTY))
                                       (VAR "b'0" BTY)))
                             (CALL "Store" (CTY "instruction")
                                   (CALL "SH" (CTY "Store")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "immediate" F16))))))
                            ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                  (BOP AND (VAR "b'1" BTY)
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "Store" (CTY "instruction")
                                   (CALL "SWL" (CTY "Store")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "immediate" F16))))))
                            ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                  (BOP AND (VAR "b'1" BTY)
                                       (VAR "b'0" BTY)))
                             (CALL "Store" (CTY "instruction")
                                   (CALL "SW" (CTY "Store")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "immediate" F16))))))
                            ((BOP AND (VAR "b'4" BTY)
                                  (BOP AND (MOP NOT (VAR "b'1" BTY))
                                       (MOP NOT (VAR "b'0" BTY))))
                             (CALL "Store" (CTY "instruction")
                                   (CALL "SC" (CTY "Store")
                                         (TP (SQBKT (VAR "rs" (FTY 5))
                                                    (VAR "rt" (FTY 5))
                                                    (VAR "immediate" F16)))))))
                     (CONST "ReservedInstruction"
                            (CTY "instruction"))))
               ((BOP AND (MOP NOT (VAR "b'4" BTY))
                     (BOP AND (MOP NOT (VAR "b'1" BTY))
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Load" (CTY "instruction")
                      (CALL "LB" (CTY "Load")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "immediate" F16))))))
               ((BOP AND (MOP NOT (VAR "b'4" BTY))
                     (BOP AND (MOP NOT (VAR "b'1" BTY))
                          (VAR "b'0" BTY)))
                (CALL "Load" (CTY "instruction")
                      (CALL "LH" (CTY "Load")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "immediate" F16))))))
               ((BOP AND (MOP NOT (VAR "b'4" BTY))
                     (BOP AND (VAR "b'1" BTY)
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Load" (CTY "instruction")
                      (CALL "LWL" (CTY "Load")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "immediate" F16))))))
               ((BOP AND (MOP NOT (VAR "b'4" BTY))
                     (BOP AND (VAR "b'1" BTY)
                          (VAR "b'0" BTY)))
                (CALL "Load" (CTY "instruction")
                      (CALL "LW" (CTY "Load")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "immediate" F16))))))
               ((BOP AND (VAR "b'4" BTY)
                     (BOP AND (MOP NOT (VAR "b'1" BTY))
                          (MOP NOT (VAR "b'0" BTY))))
                (CALL "Load" (CTY "instruction")
                      (CALL "LL" (CTY "Load")
                            (TP (SQBKT (VAR "rs" (FTY 5))
                                       (VAR "rt" (FTY 5))
                                       (VAR "immediate" F16)))))))
              (CONST "ReservedInstruction"
                     (CTY "instruction"))))
            ((VAR "b'1" BTY)
             (ITB
              (SQBKT
                ((VAR "b'0" BTY)
                 (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (VAR "b'2" BTY)))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BGTZ" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (MOP NOT (VAR "b'2" BTY))))
                              (CALL "ArithI" (CTY "instruction")
                                    (CALL "SLTIU" (CTY "ArithI")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (VAR "b'2" BTY)))
                              (CALL "ArithI" (CTY "instruction")
                                    (CALL "LUI" (CTY "ArithI")
                                          (TP (SQBKT (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (VAR "b'2" BTY)))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BGTZL" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (VAR "b'3" BTY)
                                        (MOP NOT (VAR "b'2" BTY))))
                              (CALL "Load" (CTY "instruction")
                                    (CALL "LDR" (CTY "Load")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16)))))))
                      (CONST "ReservedInstruction"
                             (CTY "instruction"))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (VAR "b'2" BTY)))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BLEZ" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (MOP NOT (VAR "b'2" BTY))))
                 (CALL "ArithI" (CTY "instruction")
                       (CALL "SLTI" (CTY "ArithI")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "rt" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (VAR "b'2" BTY)))
                 (CALL "ArithI" (CTY "instruction")
                       (CALL "XORI" (CTY "ArithI")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "rt" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (VAR "b'4" BTY)
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (VAR "b'2" BTY)))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BLEZL" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (VAR "b'4" BTY)
                      (BOP AND (VAR "b'3" BTY)
                           (MOP NOT (VAR "b'2" BTY))))
                 (CALL "Load" (CTY "instruction")
                       (CALL "LDL" (CTY "Load")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "rt" (FTY 5))
                                        (VAR "immediate" F16)))))))
              (CONST "ReservedInstruction"
                     (CTY "instruction"))))
            ((VAR "b'0" BTY)
             (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                               (BOP AND (MOP NOT (VAR "b'3" BTY))
                                    (VAR "b'2" BTY)))
                          (CALL "Branch" (CTY "instruction")
                                (CALL "BNE" (CTY "Branch")
                                      (TP (SQBKT (VAR "rs" (FTY 5))
                                                 (VAR "rt" (FTY 5))
                                                 (VAR "immediate" F16))))))
                         ((BOP AND (MOP NOT (VAR "b'4" BTY))
                               (BOP AND (VAR "b'3" BTY)
                                    (MOP NOT (VAR "b'2" BTY))))
                          (CALL "ArithI" (CTY "instruction")
                                (CALL "ADDIU" (CTY "ArithI")
                                      (TP (SQBKT (VAR "rs" (FTY 5))
                                                 (VAR "rt" (FTY 5))
                                                 (VAR "immediate" F16))))))
                         ((BOP AND (MOP NOT (VAR "b'4" BTY))
                               (BOP AND (VAR "b'3" BTY)
                                    (VAR "b'2" BTY)))
                          (CALL "ArithI" (CTY "instruction")
                                (CALL "ORI" (CTY "ArithI")
                                      (TP (SQBKT (VAR "rs" (FTY 5))
                                                 (VAR "rt" (FTY 5))
                                                 (VAR "immediate" F16))))))
                         ((BOP AND (VAR "b'4" BTY)
                               (BOP AND (MOP NOT (VAR "b'3" BTY))
                                    (VAR "b'2" BTY)))
                          (CALL "Branch" (CTY "instruction")
                                (CALL "BNEL" (CTY "Branch")
                                      (TP (SQBKT (VAR "rs" (FTY 5))
                                                 (VAR "rt" (FTY 5))
                                                 (VAR "immediate" F16))))))
                         ((BOP AND (VAR "b'4" BTY)
                               (BOP AND (VAR "b'3" BTY)
                                    (MOP NOT (VAR "b'2" BTY))))
                          (CALL "ArithI" (CTY "instruction")
                                (CALL "DADDIU" (CTY "ArithI")
                                      (TP (SQBKT (VAR "rs" (FTY 5))
                                                 (VAR "rt" (FTY 5))
                                                 (VAR "immediate" F16)))))))
                  (CONST "ReservedInstruction"
                         (CTY "instruction"))))
            ((BOP AND (MOP NOT (VAR "b'4" BTY))
                  (BOP AND (MOP NOT (VAR "b'3" BTY))
                       (VAR "b'2" BTY)))
             (CALL "Branch" (CTY "instruction")
                   (CALL "BEQ" (CTY "Branch")
                         (TP (SQBKT (VAR "rs" (FTY 5))
                                    (VAR "rt" (FTY 5))
                                    (VAR "immediate" F16))))))
            ((BOP AND (MOP NOT (VAR "b'4" BTY))
                  (BOP AND (VAR "b'3" BTY)
                       (MOP NOT (VAR "b'2" BTY))))
             (CALL "ArithI" (CTY "instruction")
                   (CALL "ADDI" (CTY "ArithI")
                         (TP (SQBKT (VAR "rs" (FTY 5))
                                    (VAR "rt" (FTY 5))
                                    (VAR "immediate" F16))))))
            ((BOP AND (MOP NOT (VAR "b'4" BTY))
                  (BOP AND (VAR "b'3" BTY)
                       (VAR "b'2" BTY)))
             (CALL "ArithI" (CTY "instruction")
                   (CALL "ANDI" (CTY "ArithI")
                         (TP (SQBKT (VAR "rs" (FTY 5))
                                    (VAR "rt" (FTY 5))
                                    (VAR "immediate" F16))))))
            ((BOP AND (VAR "b'4" BTY)
                  (BOP AND (MOP NOT (VAR "b'3" BTY))
                       (VAR "b'2" BTY)))
             (CALL "Branch" (CTY "instruction")
                   (CALL "BEQL" (CTY "Branch")
                         (TP (SQBKT (VAR "rs" (FTY 5))
                                    (VAR "rt" (FTY 5))
                                    (VAR "immediate" F16))))))
            ((BOP AND (VAR "b'4" BTY)
                  (BOP AND (VAR "b'3" BTY)
                       (MOP NOT (VAR "b'2" BTY))))
             (CALL "ArithI" (CTY "instruction")
                   (CALL "DADDI" (CTY "ArithI")
                         (TP (SQBKT (VAR "rs" (FTY 5))
                                    (VAR "rt" (FTY 5))
                                    (VAR "immediate" F16)))))))
           (CONST "ReservedInstruction"
                  (CTY "instruction"))))))))
     (LET
      (VAR "rt" (FTY 5))
      (EX (VAR "w" F32)
          (LN 20)
          (LN 16)
          (FTY 5))
      (LET
       (VAR "rs" (FTY 5))
       (EX (VAR "w" F32)
           (LN 25)
           (LN 21)
           (FTY 5))
       (LET
        (VAR "immediate" F16)
        (EX (VAR "w" F32) (LN 15) (LN 0) F16)
        (LET
         (TP (SQBKT (VAR "b'5" BTY)
                    (VAR "b'4" BTY)
                    (VAR "b'3" BTY)
                    (VAR "b'2" BTY)
                    (VAR "b'1" BTY)
                    (VAR "b'0" BTY)))
         (BL 6
             (EX (VAR "w" F32)
                 (LN 31)
                 (LN 26)
                 (FTY 6)))
         (ITB
          (SQBKT
           ((VAR "b'5" BTY)
            (ITB
             (SQBKT
              ((VAR "b'2" BTY)
               (ITB
                (SQBKT
                 ((VAR "b'3" BTY)
                  (ITB
                      (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'1" BTY))
                                        (MOP NOT (VAR "b'0" BTY))))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SDL" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'1" BTY))
                                        (VAR "b'0" BTY)))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SDR" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'1" BTY)
                                        (MOP NOT (VAR "b'0" BTY))))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SWR" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (MOP NOT (VAR "b'1" BTY))
                                        (MOP NOT (VAR "b'0" BTY))))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SCD" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (VAR "b'1" BTY)
                                        (VAR "b'0" BTY)))
                              (CALL "Store" (CTY "instruction")
                                    (CALL "SD" (CTY "Store")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16)))))))
                      (CONST "ReservedInstruction"
                             (CTY "instruction"))))
                 ((BOP AND (MOP NOT (VAR "b'4" BTY))
                       (BOP AND (MOP NOT (VAR "b'1" BTY))
                            (MOP NOT (VAR "b'0" BTY))))
                  (CALL "Load" (CTY "instruction")
                        (CALL "LBU" (CTY "Load")
                              (TP (SQBKT (VAR "rs" (FTY 5))
                                         (VAR "rt" (FTY 5))
                                         (VAR "immediate" F16))))))
                 ((BOP AND (MOP NOT (VAR "b'4" BTY))
                       (BOP AND (MOP NOT (VAR "b'1" BTY))
                            (VAR "b'0" BTY)))
                  (CALL "Load" (CTY "instruction")
                        (CALL "LHU" (CTY "Load")
                              (TP (SQBKT (VAR "rs" (FTY 5))
                                         (VAR "rt" (FTY 5))
                                         (VAR "immediate" F16))))))
                 ((BOP AND (MOP NOT (VAR "b'4" BTY))
                       (BOP AND (VAR "b'1" BTY)
                            (MOP NOT (VAR "b'0" BTY))))
                  (CALL "Load" (CTY "instruction")
                        (CALL "LWR" (CTY "Load")
                              (TP (SQBKT (VAR "rs" (FTY 5))
                                         (VAR "rt" (FTY 5))
                                         (VAR "immediate" F16))))))
                 ((BOP AND (MOP NOT (VAR "b'4" BTY))
                       (BOP AND (VAR "b'1" BTY)
                            (VAR "b'0" BTY)))
                  (CALL "Load" (CTY "instruction")
                        (CALL "LWU" (CTY "Load")
                              (TP (SQBKT (VAR "rs" (FTY 5))
                                         (VAR "rt" (FTY 5))
                                         (VAR "immediate" F16))))))
                 ((BOP AND (VAR "b'4" BTY)
                       (BOP AND (MOP NOT (VAR "b'1" BTY))
                            (MOP NOT (VAR "b'0" BTY))))
                  (CALL "Load" (CTY "instruction")
                        (CALL "LLD" (CTY "Load")
                              (TP (SQBKT (VAR "rs" (FTY 5))
                                         (VAR "rt" (FTY 5))
                                         (VAR "immediate" F16))))))
                 ((BOP AND (VAR "b'4" BTY)
                       (BOP AND (VAR "b'1" BTY)
                            (VAR "b'0" BTY)))
                  (CALL "Load" (CTY "instruction")
                        (CALL "LD" (CTY "Load")
                              (TP (SQBKT (VAR "rs" (FTY 5))
                                         (VAR "rt" (FTY 5))
                                         (VAR "immediate" F16)))))))
                (CONST "ReservedInstruction"
                       (CTY "instruction"))))
              ((VAR "b'3" BTY)
               (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                 (BOP AND (MOP NOT (VAR "b'1" BTY))
                                      (MOP NOT (VAR "b'0" BTY))))
                            (CALL "Store" (CTY "instruction")
                                  (CALL "SB" (CTY "Store")
                                        (TP (SQBKT (VAR "rs" (FTY 5))
                                                   (VAR "rt" (FTY 5))
                                                   (VAR "immediate" F16))))))
                           ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                 (BOP AND (MOP NOT (VAR "b'1" BTY))
                                      (VAR "b'0" BTY)))
                            (CALL "Store" (CTY "instruction")
                                  (CALL "SH" (CTY "Store")
                                        (TP (SQBKT (VAR "rs" (FTY 5))
                                                   (VAR "rt" (FTY 5))
                                                   (VAR "immediate" F16))))))
                           ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                 (BOP AND (VAR "b'1" BTY)
                                      (MOP NOT (VAR "b'0" BTY))))
                            (CALL "Store" (CTY "instruction")
                                  (CALL "SWL" (CTY "Store")
                                        (TP (SQBKT (VAR "rs" (FTY 5))
                                                   (VAR "rt" (FTY 5))
                                                   (VAR "immediate" F16))))))
                           ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                 (BOP AND (VAR "b'1" BTY)
                                      (VAR "b'0" BTY)))
                            (CALL "Store" (CTY "instruction")
                                  (CALL "SW" (CTY "Store")
                                        (TP (SQBKT (VAR "rs" (FTY 5))
                                                   (VAR "rt" (FTY 5))
                                                   (VAR "immediate" F16))))))
                           ((BOP AND (VAR "b'4" BTY)
                                 (BOP AND (MOP NOT (VAR "b'1" BTY))
                                      (MOP NOT (VAR "b'0" BTY))))
                            (CALL "Store" (CTY "instruction")
                                  (CALL "SC" (CTY "Store")
                                        (TP (SQBKT (VAR "rs" (FTY 5))
                                                   (VAR "rt" (FTY 5))
                                                   (VAR "immediate" F16)))))))
                    (CONST "ReservedInstruction"
                           (CTY "instruction"))))
              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                         (MOP NOT (VAR "b'0" BTY))))
               (CALL "Load" (CTY "instruction")
                     (CALL "LB" (CTY "Load")
                           (TP (SQBKT (VAR "rs" (FTY 5))
                                      (VAR "rt" (FTY 5))
                                      (VAR "immediate" F16))))))
              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                         (VAR "b'0" BTY)))
               (CALL "Load" (CTY "instruction")
                     (CALL "LH" (CTY "Load")
                           (TP (SQBKT (VAR "rs" (FTY 5))
                                      (VAR "rt" (FTY 5))
                                      (VAR "immediate" F16))))))
              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                    (BOP AND (VAR "b'1" BTY)
                         (MOP NOT (VAR "b'0" BTY))))
               (CALL "Load" (CTY "instruction")
                     (CALL "LWL" (CTY "Load")
                           (TP (SQBKT (VAR "rs" (FTY 5))
                                      (VAR "rt" (FTY 5))
                                      (VAR "immediate" F16))))))
              ((BOP AND (MOP NOT (VAR "b'4" BTY))
                    (BOP AND (VAR "b'1" BTY)
                         (VAR "b'0" BTY)))
               (CALL "Load" (CTY "instruction")
                     (CALL "LW" (CTY "Load")
                           (TP (SQBKT (VAR "rs" (FTY 5))
                                      (VAR "rt" (FTY 5))
                                      (VAR "immediate" F16))))))
              ((BOP AND (VAR "b'4" BTY)
                    (BOP AND (MOP NOT (VAR "b'1" BTY))
                         (MOP NOT (VAR "b'0" BTY))))
               (CALL "Load" (CTY "instruction")
                     (CALL "LL" (CTY "Load")
                           (TP (SQBKT (VAR "rs" (FTY 5))
                                      (VAR "rt" (FTY 5))
                                      (VAR "immediate" F16)))))))
             (CONST "ReservedInstruction"
                    (CTY "instruction"))))
           ((VAR "b'1" BTY)
            (ITB
             (SQBKT
                ((VAR "b'0" BTY)
                 (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (VAR "b'2" BTY)))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BGTZ" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (MOP NOT (VAR "b'2" BTY))))
                              (CALL "ArithI" (CTY "instruction")
                                    (CALL "SLTIU" (CTY "ArithI")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (MOP NOT (VAR "b'4" BTY))
                                   (BOP AND (VAR "b'3" BTY)
                                        (VAR "b'2" BTY)))
                              (CALL "ArithI" (CTY "instruction")
                                    (CALL "LUI" (CTY "ArithI")
                                          (TP (SQBKT (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (MOP NOT (VAR "b'3" BTY))
                                        (VAR "b'2" BTY)))
                              (CALL "Branch" (CTY "instruction")
                                    (CALL "BGTZL" (CTY "Branch")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "immediate" F16))))))
                             ((BOP AND (VAR "b'4" BTY)
                                   (BOP AND (VAR "b'3" BTY)
                                        (MOP NOT (VAR "b'2" BTY))))
                              (CALL "Load" (CTY "instruction")
                                    (CALL "LDR" (CTY "Load")
                                          (TP (SQBKT (VAR "rs" (FTY 5))
                                                     (VAR "rt" (FTY 5))
                                                     (VAR "immediate" F16)))))))
                      (CONST "ReservedInstruction"
                             (CTY "instruction"))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (VAR "b'2" BTY)))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BLEZ" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (MOP NOT (VAR "b'2" BTY))))
                 (CALL "ArithI" (CTY "instruction")
                       (CALL "SLTI" (CTY "ArithI")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "rt" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (MOP NOT (VAR "b'4" BTY))
                      (BOP AND (VAR "b'3" BTY)
                           (VAR "b'2" BTY)))
                 (CALL "ArithI" (CTY "instruction")
                       (CALL "XORI" (CTY "ArithI")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "rt" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (VAR "b'4" BTY)
                      (BOP AND (MOP NOT (VAR "b'3" BTY))
                           (VAR "b'2" BTY)))
                 (CALL "Branch" (CTY "instruction")
                       (CALL "BLEZL" (CTY "Branch")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "immediate" F16))))))
                ((BOP AND (VAR "b'4" BTY)
                      (BOP AND (VAR "b'3" BTY)
                           (MOP NOT (VAR "b'2" BTY))))
                 (CALL "Load" (CTY "instruction")
                       (CALL "LDL" (CTY "Load")
                             (TP (SQBKT (VAR "rs" (FTY 5))
                                        (VAR "rt" (FTY 5))
                                        (VAR "immediate" F16)))))))
             (CONST "ReservedInstruction"
                    (CTY "instruction"))))
           ((VAR "b'0" BTY)
            (ITB (SQBKT ((BOP AND (MOP NOT (VAR "b'4" BTY))
                              (BOP AND (MOP NOT (VAR "b'3" BTY))
                                   (VAR "b'2" BTY)))
                         (CALL "Branch" (CTY "instruction")
                               (CALL "BNE" (CTY "Branch")
                                     (TP (SQBKT (VAR "rs" (FTY 5))
                                                (VAR "rt" (FTY 5))
                                                (VAR "immediate" F16))))))
                        ((BOP AND (MOP NOT (VAR "b'4" BTY))
                              (BOP AND (VAR "b'3" BTY)
                                   (MOP NOT (VAR "b'2" BTY))))
                         (CALL "ArithI" (CTY "instruction")
                               (CALL "ADDIU" (CTY "ArithI")
                                     (TP (SQBKT (VAR "rs" (FTY 5))
                                                (VAR "rt" (FTY 5))
                                                (VAR "immediate" F16))))))
                        ((BOP AND (MOP NOT (VAR "b'4" BTY))
                              (BOP AND (VAR "b'3" BTY)
                                   (VAR "b'2" BTY)))
                         (CALL "ArithI" (CTY "instruction")
                               (CALL "ORI" (CTY "ArithI")
                                     (TP (SQBKT (VAR "rs" (FTY 5))
                                                (VAR "rt" (FTY 5))
                                                (VAR "immediate" F16))))))
                        ((BOP AND (VAR "b'4" BTY)
                              (BOP AND (MOP NOT (VAR "b'3" BTY))
                                   (VAR "b'2" BTY)))
                         (CALL "Branch" (CTY "instruction")
                               (CALL "BNEL" (CTY "Branch")
                                     (TP (SQBKT (VAR "rs" (FTY 5))
                                                (VAR "rt" (FTY 5))
                                                (VAR "immediate" F16))))))
                        ((BOP AND (VAR "b'4" BTY)
                              (BOP AND (VAR "b'3" BTY)
                                   (MOP NOT (VAR "b'2" BTY))))
                         (CALL "ArithI" (CTY "instruction")
                               (CALL "DADDIU" (CTY "ArithI")
                                     (TP (SQBKT (VAR "rs" (FTY 5))
                                                (VAR "rt" (FTY 5))
                                                (VAR "immediate" F16)))))))
                 (CONST "ReservedInstruction"
                        (CTY "instruction"))))
           ((BOP AND (MOP NOT (VAR "b'4" BTY))
                 (BOP AND (MOP NOT (VAR "b'3" BTY))
                      (VAR "b'2" BTY)))
            (CALL "Branch" (CTY "instruction")
                  (CALL "BEQ" (CTY "Branch")
                        (TP (SQBKT (VAR "rs" (FTY 5))
                                   (VAR "rt" (FTY 5))
                                   (VAR "immediate" F16))))))
           ((BOP AND (MOP NOT (VAR "b'4" BTY))
                 (BOP AND (VAR "b'3" BTY)
                      (MOP NOT (VAR "b'2" BTY))))
            (CALL "ArithI" (CTY "instruction")
                  (CALL "ADDI" (CTY "ArithI")
                        (TP (SQBKT (VAR "rs" (FTY 5))
                                   (VAR "rt" (FTY 5))
                                   (VAR "immediate" F16))))))
           ((BOP AND (MOP NOT (VAR "b'4" BTY))
                 (BOP AND (VAR "b'3" BTY)
                      (VAR "b'2" BTY)))
            (CALL "ArithI" (CTY "instruction")
                  (CALL "ANDI" (CTY "ArithI")
                        (TP (SQBKT (VAR "rs" (FTY 5))
                                   (VAR "rt" (FTY 5))
                                   (VAR "immediate" F16))))))
           ((BOP AND (VAR "b'4" BTY)
                 (BOP AND (MOP NOT (VAR "b'3" BTY))
                      (VAR "b'2" BTY)))
            (CALL "Branch" (CTY "instruction")
                  (CALL "BEQL" (CTY "Branch")
                        (TP (SQBKT (VAR "rs" (FTY 5))
                                   (VAR "rt" (FTY 5))
                                   (VAR "immediate" F16))))))
           ((BOP AND (VAR "b'4" BTY)
                 (BOP AND (VAR "b'3" BTY)
                      (MOP NOT (VAR "b'2" BTY))))
            (CALL "ArithI" (CTY "instruction")
                  (CALL "DADDI" (CTY "ArithI")
                        (TP (SQBKT (VAR "rs" (FTY 5))
                                   (VAR "rt" (FTY 5))
                                   (VAR "immediate" F16)))))))
          (CONST "ReservedInstruction"
                 (CTY "instruction"))))))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "Fetch" QVAR
   (LET
    (VAR "v" F64)
    (DEST "PC" F64 QVAR)
    (LET
     (TP (SQBKT (VAR "pAddr" F64)
                (VAR "CCA" (FTY 3))))
     (CALL "AddressTranslation" (PTY F64 (FTY 3))
           (TP (SQBKT (VAR "v" F64)
                      (LC "INSTRUCTION" (CTY "IorD"))
                      (LC "LOAD" (CTY "LorS")))))
     (LET
      (VAR "v0" (FTY 3))
      (BOP BXOR
           (EX (VAR "v" F64) (LN 2) (LN 0) (FTY 3))
           (CC (SQBKT (MOP FST
                           (APPLY (CONST "BigEndianCPU" (ATY QTY (PTY F1 QTY)))
                                  QVAR))
                      (LW 0 2))))
      (TP
        (SQBKT
             (EX (MOP FST
                      (APPLY (CALL "LoadMemory" (ATY QTY (PTY F64 QTY))
                                   (TP (SQBKT (VAR "CCA" (FTY 3))
                                              (CONST "WORD" (FTY 3))
                                              (VAR "pAddr" F64)
                                              (VAR "v" F64)
                                              (LC "INSTRUCTION" (CTY "IorD")))))
                             QVAR))
                 (BOP ADD (LN 31)
                      (BOP MUL (LN 8)
                           (MOP (CAST NTY) (VAR "v0" (FTY 3)))))
                 (BOP MUL (LN 8)
                      (MOP (CAST NTY) (VAR "v0" (FTY 3))))
                 F32)
             QVAR))))))))

(VALUE-TRIPLE
 (LIST
  :ERROR
  (DEF
   "Next" QVAR
   (LET
    QVAR
    (MOP SND
         (APPLY (CALL "Run" (ATY QTY (PTY UTY QTY))
                      (CALL "Decode" (CTY "instruction")
                            (MOP FST
                                 (APPLY (CONST "Fetch" (ATY QTY (PTY F32 QTY)))
                                        QVAR))))
                (RUPD "BranchStatus"
                      (TP (SQBKT QVAR (LO F64))))))
    (LET
     QVAR
     (CS (DEST "BranchStatus" (OTY F64) QVAR)
         (SQBKT ((MOP SOME (VAR "addr" F64))
                 (ITE (MOP ISSOME
                           (DEST "BranchStatus" (OTY F64) QVAR))
                      (MOP SND
                           (APPLY (CALL "raise'exception"
                                        (ATY QTY (PTY UTY QTY))
                                        (CALL "UNPREDICTABLE" (CTY "exception")
                                              (LS "Branch follows branch")))
                                  QVAR))
                      (RUPD "PC"
                            (TP (SQBKT QVAR (VAR "addr" F64))))))
                ((LO F64) QVAR)))
     (LET
      QVAR
      (RUPD "PC"
            (TP (SQBKT QVAR
                       (BOP ADD (DEST "PC" F64 QVAR)
                            (LW 4 64)))))
      (TP
       (SQBKT
        LU
        (RUPD
         "CP0"
         (TP
           (SQBKT QVAR
                  (RUPD "Count"
                        (TP (SQBKT (DEST "CP0" (CTY "CP0") QVAR)
                                   (BOP ADD
                                        (DEST "Count"
                                              F32 (DEST "CP0" (CTY "CP0") QVAR))
                                        (LW 1 32))))))))))))))))

