(C::EXEC-ARRSUB-OF-MEMBER
 (16 2 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (13 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (10 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (8 2 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (5 1 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (3 3 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (3 3 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-VAR-TABLE-SCOPEP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-TAG-ENVP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-SCOPEP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-TABLEP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-ENVP-BINDS-FREE-X))
 (2 2 (:TYPE-PRESCRIPTION C::VALUEP))
 )
(C::EXPR-VALUE-RESULTP-OF-EXEC-ARRSUB-OF-MEMBER)
(C::EXEC-ARRSUB-OF-MEMBER-OF-EXPR-VALUE-FIX-STR)
(C::EXEC-ARRSUB-OF-MEMBER-EXPR-VALUE-EQUIV-CONGRUENCE-ON-STR)
(C::EXEC-ARRSUB-OF-MEMBER-OF-IDENT-FIX-MEM
 (9 1 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (1 1 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::IDENTP-WHEN-ASSOC-VAR-TABLE-SCOPEP-BINDS-FREE-X))
 (1 1 (:REWRITE C::IDENTP-WHEN-ASSOC-TAG-ENVP-BINDS-FREE-X))
 (1 1 (:REWRITE C::IDENTP-WHEN-ASSOC-SCOPEP-BINDS-FREE-X))
 (1 1 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-TABLEP-BINDS-FREE-X))
 (1 1 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-ENVP-BINDS-FREE-X))
 )
(C::EXEC-ARRSUB-OF-MEMBER-IDENT-EQUIV-CONGRUENCE-ON-MEM)
(C::EXEC-ARRSUB-OF-MEMBER-OF-EXPR-VALUE-FIX-SUB
 (64 8 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (40 8 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (24 24 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (16 16 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (16 8 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (9 3 (:REWRITE C::EXPR-VALUE-FIX-WHEN-EXPR-VALUEP))
 (6 6 (:TYPE-PRESCRIPTION C::EXPR-VALUEP))
 (4 4 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 )
(C::EXEC-ARRSUB-OF-MEMBER-EXPR-VALUE-EQUIV-CONGRUENCE-ON-SUB)
(C::EXEC-ARRSUB-OF-MEMBER-OF-COMPUSTATE-FIX-COMPST
 (59 11 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (26 11 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (22 22 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (4 4 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 )
(C::EXEC-ARRSUB-OF-MEMBER-COMPUSTATE-EQUIV-CONGRUENCE-ON-COMPST)
(C::EXEC-ARRSUB-OF-MEMBERP)
(C::EXPR-VALUE-RESULTP-OF-EXEC-ARRSUB-OF-MEMBERP)
(C::EXEC-ARRSUB-OF-MEMBERP-OF-EXPR-VALUE-FIX-STR)
(C::EXEC-ARRSUB-OF-MEMBERP-EXPR-VALUE-EQUIV-CONGRUENCE-ON-STR)
(C::EXEC-ARRSUB-OF-MEMBERP-OF-IDENT-FIX-MEM
 (64 8 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (40 8 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (24 24 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (16 16 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (16 8 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-VAR-TABLE-SCOPEP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-TAG-ENVP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-SCOPEP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-TABLEP-BINDS-FREE-X))
 (3 3 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-ENVP-BINDS-FREE-X))
 (1 1 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::EXEC-ARRSUB-OF-MEMBERP-IDENT-EQUIV-CONGRUENCE-ON-MEM)
(C::EXEC-ARRSUB-OF-MEMBERP-OF-EXPR-VALUE-FIX-SUB
 (64 8 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (40 8 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (24 24 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (16 16 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (16 8 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (3 1 (:REWRITE C::EXPR-VALUE-FIX-WHEN-EXPR-VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::EXPR-VALUEP))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-VAR-TABLE-SCOPEP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-TAG-ENVP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-SCOPEP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-TABLEP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-ENVP-BINDS-FREE-X))
 )
(C::EXEC-ARRSUB-OF-MEMBERP-EXPR-VALUE-EQUIV-CONGRUENCE-ON-SUB)
(C::EXEC-ARRSUB-OF-MEMBERP-OF-COMPUSTATE-FIX-COMPST
 (49 9 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (22 9 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (18 18 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-VAR-TABLE-SCOPEP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-TAG-ENVP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-SCOPEP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-TABLEP-BINDS-FREE-X))
 (2 2 (:REWRITE C::IDENTP-WHEN-ASSOC-FUN-ENVP-BINDS-FREE-X))
 )
(C::EXEC-ARRSUB-OF-MEMBERP-COMPUSTATE-EQUIV-CONGRUENCE-ON-COMPST)
(C::EXEC-EXPR-PURE-WHEN-IDENT
 (8 1 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (5 1 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::EXPRP))
 (2 2 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (2 1 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 )
(C::EXEC-EXPR-PURE-WHEN-IDENT-NO-SYNTAXP
 (8 1 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (5 1 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::EXPRP))
 (2 2 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (2 1 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 )
(C::EXEC-EXPR-PURE-WHEN-CONST
 (8 1 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (5 1 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::EXPRP))
 (2 2 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (2 1 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 )
(C::EXEC-EXPR-PURE-WHEN-ARRSUB
 (150 150 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (140 140 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (118 11 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (80 80 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (65 11 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (60 60 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (40 40 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (32 11 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (23 23 (:TYPE-PRESCRIPTION C::EXPRP))
 (22 22 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-ARRSUB->SUB$INLINE))
 (10 10 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-ARRSUB->SUB))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-ARRSUB->ARR))
 )
(C::EXEC-EXPR-PURE-WHEN-MEMBER
 (75 75 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (70 70 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (63 6 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (40 40 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (35 6 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (30 30 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (20 20 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (17 6 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-MEMBER->TARGET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::EXPRP))
 (12 12 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (5 5 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-MEMBER->TARGET))
 )
(C::EXEC-EXPR-PURE-WHEN-MEMBER-NO-SYNTAXP
 (75 75 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (70 70 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (63 6 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (40 40 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (35 6 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (30 30 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (20 20 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (17 6 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-MEMBER->TARGET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::EXPRP))
 (12 12 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (5 5 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-MEMBER->TARGET))
 )
(C::EXEC-EXPR-PURE-WHEN-MEMBERP
 (75 75 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (70 70 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (63 6 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (40 40 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (35 6 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (30 30 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (20 20 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (17 6 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-MEMBERP->TARGET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::EXPRP))
 (12 12 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (5 5 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-MEMBERP->TARGET))
 )
(C::EXEC-EXPR-PURE-WHEN-MEMBERP-NO-SYNTAXP
 (75 75 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (70 70 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (63 6 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (40 40 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (35 6 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (30 30 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (20 20 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (17 6 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-MEMBERP->TARGET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::EXPRP))
 (12 12 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (5 5 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-MEMBERP->TARGET))
 )
(C::EXEC-EXPR-PURE-WHEN-ARRSUB-OF-MEMBER
 (19 4 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (11 11 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (11 2 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (9 3 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (7 3 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (6 6 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (6 3 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (5 2 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (4 4 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 )
(C::EXEC-EXPR-PURE-WHEN-ARRSUB-OF-MEMBER-NO-SYNTAXP
 (19 4 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (11 11 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (11 2 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (9 3 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (7 3 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (6 6 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (6 3 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (5 2 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (4 4 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 )
(C::EXEC-EXPR-PURE-WHEN-ARRSUB-OF-MEMBERP
 (228 32 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (140 28 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (84 84 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (72 72 (:TYPE-PRESCRIPTION C::TYPE-KIND$INLINE))
 (57 12 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (56 56 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (56 28 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (27 9 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (18 18 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (18 18 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (12 12 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-VOID))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-USHORT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-ULONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-ULLONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-UINT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-UCHAR))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SSHORT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SLONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SLLONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SINT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SCHAR))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-CHAR))
 (12 6 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (11 2 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (5 2 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (4 4 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 )
(C::EXEC-EXPR-PURE-WHEN-ARRSUB-OF-MEMBERP-NO-SYNTAXP
 (228 32 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (140 28 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (84 84 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (72 72 (:TYPE-PRESCRIPTION C::TYPE-KIND$INLINE))
 (57 12 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (56 56 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (56 28 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (27 9 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (18 18 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (18 18 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (12 12 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-VOID))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-USHORT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-ULONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-ULLONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-UINT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-UCHAR))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SSHORT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SLONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SLLONG))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SINT))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-SCHAR))
 (12 6 (:REWRITE C::TYPE-FIX-WHEN-CHAR))
 (12 6 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (11 2 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (5 2 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (4 4 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 )
(C::EXEC-EXPR-PURE-WHEN-UNARY
 (75 75 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (70 70 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (63 6 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (40 40 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (35 6 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (30 30 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (20 20 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (17 6 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-UNARY->ARG$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::EXPRP))
 (12 12 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (5 5 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-UNARY->ARG))
 )
(C::EXEC-EXPR-PURE-WHEN-CAST
 (75 75 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (70 70 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (63 6 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (40 40 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (35 6 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (30 30 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (20 20 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (17 6 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (15 15 (:TYPE-PRESCRIPTION C::EXPR-CAST->ARG$INLINE))
 (13 13 (:TYPE-PRESCRIPTION C::EXPRP))
 (12 12 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (5 5 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (5 5 (:REWRITE C::EXPRP-OF-EXPR-CAST->ARG))
 )
(C::EXEC-EXPR-PURE-WHEN-STRICT-PURE-BINARY
 (3057 3057 (:REWRITE SUBSETP-MEMBER . 4))
 (3057 3057 (:REWRITE SUBSETP-MEMBER . 3))
 (3057 3057 (:REWRITE SUBSETP-MEMBER . 2))
 (3057 3057 (:REWRITE SUBSETP-MEMBER . 1))
 (3057 3057 (:REWRITE INTERSECTP-MEMBER . 3))
 (3057 3057 (:REWRITE INTERSECTP-MEMBER . 2))
 (2400 2400 (:TYPE-PRESCRIPTION C::TEST-VALUE))
 (2240 2240 (:TYPE-PRESCRIPTION C::APCONVERT-EXPR-VALUE))
 (1888 176 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (1280 1280 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (1040 176 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (960 960 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (512 176 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (368 368 (:TYPE-PRESCRIPTION C::EXPRP))
 (352 352 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (240 240 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG2$INLINE))
 (240 240 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (80 80 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG2))
 (80 80 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 )
(C::SINT-FROM-BOOLEAN-WITH-ERROR)
(C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND
 (11247 1242 (:REWRITE MEMBER-OF-CONS))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 4))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 3))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 2))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 1))
 (1311 1311 (:REWRITE INTERSECTP-MEMBER . 3))
 (1311 1311 (:REWRITE INTERSECTP-MEMBER . 2))
 (767 70 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (558 558 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (420 420 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (419 70 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (209 70 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (141 141 (:TYPE-PRESCRIPTION C::EXPRP))
 (140 140 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (117 117 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (90 90 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG2$INLINE))
 (69 69 (:REWRITE MEMBER-WHEN-ATOM))
 (39 39 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 (30 30 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG2))
 )
(C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND-AND-TRUE
 (7009 774 (:REWRITE MEMBER-OF-CONS))
 (817 817 (:REWRITE SUBSETP-MEMBER . 4))
 (817 817 (:REWRITE SUBSETP-MEMBER . 3))
 (817 817 (:REWRITE SUBSETP-MEMBER . 2))
 (817 817 (:REWRITE SUBSETP-MEMBER . 1))
 (817 817 (:REWRITE INTERSECTP-MEMBER . 3))
 (817 817 (:REWRITE INTERSECTP-MEMBER . 2))
 (481 44 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (347 347 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (263 44 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (260 260 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (131 44 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (89 89 (:TYPE-PRESCRIPTION C::EXPRP))
 (88 88 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (69 69 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG2$INLINE))
 (60 60 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (43 43 (:REWRITE MEMBER-WHEN-ATOM))
 (23 23 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG2))
 (20 20 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 (14 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (6 1 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION C::SINT-FROM-BOOLEAN))
 (3 3 (:TYPE-PRESCRIPTION C::VALUEP))
 (3 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (2 2 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 )
(C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND-AND-FALSE
 (1304 144 (:REWRITE MEMBER-OF-CONS))
 (152 152 (:REWRITE SUBSETP-MEMBER . 4))
 (152 152 (:REWRITE SUBSETP-MEMBER . 3))
 (152 152 (:REWRITE SUBSETP-MEMBER . 2))
 (152 152 (:REWRITE SUBSETP-MEMBER . 1))
 (152 152 (:REWRITE INTERSECTP-MEMBER . 3))
 (152 152 (:REWRITE INTERSECTP-MEMBER . 2))
 (96 9 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (65 65 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (53 9 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (49 49 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (26 9 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (24 24 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (19 19 (:TYPE-PRESCRIPTION C::EXPRP))
 (18 18 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (8 8 (:REWRITE MEMBER-WHEN-ATOM))
 (8 8 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 )
(C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR
 (11247 1242 (:REWRITE MEMBER-OF-CONS))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 4))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 3))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 2))
 (1311 1311 (:REWRITE SUBSETP-MEMBER . 1))
 (1311 1311 (:REWRITE INTERSECTP-MEMBER . 3))
 (1311 1311 (:REWRITE INTERSECTP-MEMBER . 2))
 (767 70 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (558 558 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (420 420 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (419 70 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (209 70 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (141 141 (:TYPE-PRESCRIPTION C::EXPRP))
 (140 140 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (117 117 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (90 90 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG2$INLINE))
 (69 69 (:REWRITE MEMBER-WHEN-ATOM))
 (39 39 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 (30 30 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG2))
 )
(C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR-AND-TRUE
 (1304 144 (:REWRITE MEMBER-OF-CONS))
 (152 152 (:REWRITE SUBSETP-MEMBER . 4))
 (152 152 (:REWRITE SUBSETP-MEMBER . 3))
 (152 152 (:REWRITE SUBSETP-MEMBER . 2))
 (152 152 (:REWRITE SUBSETP-MEMBER . 1))
 (152 152 (:REWRITE INTERSECTP-MEMBER . 3))
 (152 152 (:REWRITE INTERSECTP-MEMBER . 2))
 (96 9 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (65 65 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (53 9 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (49 49 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (26 9 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (24 24 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (19 19 (:TYPE-PRESCRIPTION C::EXPRP))
 (18 18 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (8 8 (:REWRITE MEMBER-WHEN-ATOM))
 (8 8 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 )
(C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR-AND-FALSE
 (6683 738 (:REWRITE MEMBER-OF-CONS))
 (779 779 (:REWRITE SUBSETP-MEMBER . 4))
 (779 779 (:REWRITE SUBSETP-MEMBER . 3))
 (779 779 (:REWRITE SUBSETP-MEMBER . 2))
 (779 779 (:REWRITE SUBSETP-MEMBER . 1))
 (779 779 (:REWRITE INTERSECTP-MEMBER . 3))
 (779 779 (:REWRITE INTERSECTP-MEMBER . 2))
 (459 42 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (331 331 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (251 42 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (248 248 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (125 42 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (85 85 (:TYPE-PRESCRIPTION C::EXPRP))
 (84 84 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (69 69 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG2$INLINE))
 (54 54 (:TYPE-PRESCRIPTION C::EXPR-BINARY->ARG1$INLINE))
 (41 41 (:REWRITE MEMBER-WHEN-ATOM))
 (23 23 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG2))
 (18 18 (:REWRITE C::EXPRP-OF-EXPR-BINARY->ARG1))
 (14 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (6 1 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION C::SINT-FROM-BOOLEAN))
 (3 3 (:TYPE-PRESCRIPTION C::VALUEP))
 (3 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (2 2 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 )
(C::SINT-FROM-BOOLEAN-WITH-ERROR-WHEN-BOOLEANP
 (2 2 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 )
(C::SINT-FROM-BOOLEAN-WITH-ERROR-WHEN-BOOLEANP-AND-TRUE)
(C::SINT-FROM-BOOLEAN-WITH-ERROR-WHEN-BOOLEANP-AND-FALSE)
(C::EXEC-EXPR-PURE-APCONVERT-NO-OBJECT)
(C::EXEC-EXPR-PURE-APCONVERT-NO-OBJECT-OPEN
 (2 2 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 )
(C::EXEC-EXPR-PURE-WHEN-COND
 (239 22 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (174 174 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (131 22 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (126 126 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (84 84 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (65 22 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (45 45 (:TYPE-PRESCRIPTION C::EXPRP))
 (44 44 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (27 27 (:TYPE-PRESCRIPTION C::EXPR-COND->TEST$INLINE))
 (21 21 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (18 18 (:TYPE-PRESCRIPTION C::EXPR-COND->THEN$INLINE))
 (18 18 (:TYPE-PRESCRIPTION C::EXPR-COND->ELSE$INLINE))
 (9 9 (:REWRITE C::EXPRP-OF-EXPR-COND->TEST))
 (6 6 (:REWRITE C::EXPRP-OF-EXPR-COND->THEN))
 (6 6 (:REWRITE C::EXPRP-OF-EXPR-COND->ELSE))
 )
(C::EXEC-EXPR-PURE-WHEN-COND-AND-TRUE
 (316 29 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (227 227 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (173 29 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (168 168 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (112 112 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (86 29 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (59 59 (:TYPE-PRESCRIPTION C::EXPRP))
 (58 58 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (42 42 (:TYPE-PRESCRIPTION C::EXPR-COND->THEN$INLINE))
 (42 42 (:TYPE-PRESCRIPTION C::EXPR-COND->TEST$INLINE))
 (28 28 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (14 14 (:REWRITE C::EXPRP-OF-EXPR-COND->THEN))
 (14 14 (:REWRITE C::EXPRP-OF-EXPR-COND->TEST))
 )
(C::EXEC-EXPR-PURE-WHEN-COND-AND-FALSE
 (305 28 (:REWRITE C::EXPR-FIX-WHEN-EXPRP))
 (219 219 (:REWRITE-QUOTED-CONSTANT C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV))
 (167 28 (:REWRITE C::EXPRP-WHEN-EXPR-OPTIONP))
 (162 162 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (108 108 (:TYPE-PRESCRIPTION C::BINOP-KIND$INLINE))
 (83 28 (:REWRITE C::EXPR-OPTIONP-WHEN-EXPRP))
 (57 57 (:TYPE-PRESCRIPTION C::EXPRP))
 (56 56 (:TYPE-PRESCRIPTION C::EXPR-OPTIONP))
 (42 42 (:TYPE-PRESCRIPTION C::EXPR-COND->ELSE$INLINE))
 (39 39 (:TYPE-PRESCRIPTION C::EXPR-COND->TEST$INLINE))
 (27 27 (:TYPE-PRESCRIPTION C::BINOP-PUREP))
 (14 14 (:REWRITE C::EXPRP-OF-EXPR-COND->ELSE))
 (13 13 (:REWRITE C::EXPRP-OF-EXPR-COND->TEST))
 )
(C::EXEC-EXPR-PURE-LIST-OF-NIL
 (1 1 (:REWRITE-QUOTED-CONSTANT C::EXPR-LIST-FIX-UNDER-EXPR-LIST-EQUIV))
 )
(C::EXEC-EXPR-PURE-LIST-WHEN-CONSP
 (4 1 (:REWRITE C::VALUE-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE C::VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 )
