(RV32-JAL
 (96 3 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (53 20 (:REWRITE DEFAULT-+-2))
 (52 20 (:REWRITE DEFAULT-<-1))
 (36 20 (:REWRITE DEFAULT-+-1))
 (24 12 (:REWRITE DEFAULT-*-2))
 (24 12 (:REWRITE DEFAULT-*-1))
 (23 20 (:REWRITE DEFAULT-<-2))
 (18 3 (:DEFINITION NFIX))
 (15 1 (:REWRITE LOGAND-LESSP-24))
 (14 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE DEFAULT-NUMERATOR))
 (6 3 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(RV32P-OF-RV32-JAL
 (96 3 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (50 18 (:REWRITE DEFAULT-+-2))
 (34 12 (:REWRITE DEFAULT-<-1))
 (33 18 (:REWRITE DEFAULT-+-1))
 (24 12 (:REWRITE DEFAULT-*-2))
 (24 12 (:REWRITE DEFAULT-*-1))
 (18 3 (:DEFINITION NFIX))
 (15 12 (:REWRITE DEFAULT-<-2))
 (15 1 (:REWRITE LOGAND-LESSP-24))
 (14 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE DEFAULT-NUMERATOR))
 (6 3 (:REWRITE DEFAULT-DENOMINATOR))
 (5 2 (:LINEAR RIP-LESS-THAN-EXPT-2-32))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(RV32-JALR
 (96 3 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (53 20 (:REWRITE DEFAULT-+-2))
 (43 21 (:REWRITE DEFAULT-<-1))
 (35 20 (:REWRITE DEFAULT-+-1))
 (24 21 (:REWRITE DEFAULT-<-2))
 (24 12 (:REWRITE DEFAULT-*-2))
 (24 12 (:REWRITE DEFAULT-*-1))
 (18 3 (:DEFINITION NFIX))
 (15 1 (:REWRITE LOGAND-LESSP-24))
 (14 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 3 (:REWRITE DEFAULT-NUMERATOR))
 (6 3 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(RV32P-OF-RV32-JALR
 (96 3 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (50 18 (:REWRITE DEFAULT-+-2))
 (35 12 (:REWRITE DEFAULT-<-1))
 (34 18 (:REWRITE DEFAULT-+-1))
 (24 12 (:REWRITE DEFAULT-*-2))
 (24 12 (:REWRITE DEFAULT-*-1))
 (18 3 (:DEFINITION NFIX))
 (15 12 (:REWRITE DEFAULT-<-2))
 (15 1 (:REWRITE LOGAND-LESSP-24))
 (14 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:TYPE-PRESCRIPTION NATP-RIP))
 (6 3 (:REWRITE DEFAULT-NUMERATOR))
 (6 3 (:REWRITE DEFAULT-DENOMINATOR))
 (5 2 (:LINEAR RIP-LESS-THAN-EXPT-2-32))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(N05-WHEN-N05P
 (1 1 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(N12-WHEN-N12P
 (1 1 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(N20-WHEN-N20P
 (1 1 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(N05P-OF-N05)
(N10P-OF-N10
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (8 1 (:LINEAR N08P-LOGAND-N08P-LESS-THAN-256))
 (8 1 (:LINEAR N05P-LOGAND-N05P-LESS-THAN-32))
 (8 1 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (8 1 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (8 1 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (8 1 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 )
(N01P-OF-N01)
(N08P-OF-N08)
(ASM-JAL)
(N32P-OF-ASM-JAL-GL
 (5 5 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(N32P-OF-ASM-JAL
 (516 156 (:REWRITE DEFAULT-+-2))
 (282 156 (:REWRITE DEFAULT-+-1))
 (114 114 (:REWRITE FOLD-CONSTS-IN-+))
 (9 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE N05-WHEN-N05P))
 (4 4 (:REWRITE DEFAULT-<-2))
 )
(GET-OPCODE-OF-ASM-JAL-GL
 (5 5 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-OPCODE-OF-ASM-JAL
 (196 2 (:LINEAR N05P-LOGAND-N05P-LESS-THAN-32))
 (196 2 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (196 2 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (196 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (196 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (172 52 (:REWRITE DEFAULT-+-2))
 (142 32 (:REWRITE DEFAULT-<-1))
 (94 52 (:REWRITE DEFAULT-+-1))
 (76 2 (:DEFINITION NATP))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (32 32 (:REWRITE DEFAULT-<-2))
 (7 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE N05-WHEN-N05P))
 )
(GET-J-IMM-OF-ASM-JAL-GL
 (2 2 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-J-IMM-OF-ASM-JAL
 (172 52 (:REWRITE DEFAULT-+-2))
 (162 162 (:TYPE-PRESCRIPTION ASH))
 (94 52 (:REWRITE DEFAULT-+-1))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2 (:REWRITE N05-WHEN-N05P))
 )
(GET-RD-OF-ASM-JAL-GL
 (5 5 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-RD-OF-ASM-JAL
 (172 52 (:REWRITE DEFAULT-+-2))
 (94 52 (:REWRITE DEFAULT-+-1))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE N05-WHEN-N05P))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (8 2 (:LINEAR LOGAND-LESS-THAN-OR-EQUAL))
 (8 1 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (8 1 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (8 1 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (8 1 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (3 1 (:DEFINITION NATP))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ASM-JALR
 (76 34 (:REWRITE DEFAULT-+-2))
 (58 34 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(N32P-OF-ASM-JALR-GL
 (3 3 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(N32P-OF-ASM-JALR
 (261 108 (:REWRITE DEFAULT-+-2))
 (189 108 (:REWRITE DEFAULT-+-1))
 (54 54 (:REWRITE FOLD-CONSTS-IN-+))
 (54 45 (:REWRITE DEFAULT-<-1))
 (45 45 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE N12-WHEN-N12P))
 (18 18 (:REWRITE N05-WHEN-N05P))
 (16 2 (:LINEAR N08P-LOGAND-N08P-LESS-THAN-256))
 (16 2 (:LINEAR N05P-LOGAND-N05P-LESS-THAN-32))
 (16 2 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (16 2 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (16 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (16 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 )
(GET-OPCODE-OF-ASM-JALR-GL
 (3 3 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-FUNCT3-OF-ASM-JALR-GL
 (3 3 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-I-IMM-OF-ASM-JALR-GL
 (3 3 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-OPCODE-OF-ASM-JALR
 (160 2 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (94 5 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (94 5 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (94 5 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (94 5 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (89 5 (:LINEAR N05P-LOGAND-N05P-LESS-THAN-32))
 (88 85 (:REWRITE DEFAULT-<-1))
 (87 85 (:REWRITE DEFAULT-<-2))
 (87 36 (:REWRITE DEFAULT-+-2))
 (63 36 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE N12-WHEN-N12P))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE N05-WHEN-N05P))
 (12 12 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (10 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(GET-FUNCT3-OF-ASM-JALR
 (116 5 (:LINEAR ASH-N02P-IS-ZERO-OR-POSITIVE))
 (106 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (106 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (105 5 (:DEFINITION NATP))
 (87 36 (:REWRITE DEFAULT-+-2))
 (63 36 (:REWRITE DEFAULT-+-1))
 (55 5 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (47 47 (:TYPE-PRESCRIPTION FIX))
 (40 32 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE N12-WHEN-N12P))
 (9 9 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE N05-WHEN-N05P))
 (6 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(GET-I-IMM-OF-ASM-JALR
 (87 36 (:REWRITE DEFAULT-+-2))
 (63 36 (:REWRITE DEFAULT-+-1))
 (43 40 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE N12-WHEN-N12P))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (16 2 (:LINEAR N08P-LOGAND-N08P-LESS-THAN-256))
 (16 2 (:LINEAR N05P-LOGAND-N05P-LESS-THAN-32))
 (16 2 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (16 2 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (16 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (16 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (6 6 (:REWRITE N05-WHEN-N05P))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(GET-RS1-OF-ASM-JALR-GL
 (3 3 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-RS1-OF-ASM-JALR
 (87 36 (:REWRITE DEFAULT-+-2))
 (63 36 (:REWRITE DEFAULT-+-1))
 (37 34 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE N05-WHEN-N05P))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (16 2 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (16 2 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (16 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (16 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (14 14 (:REWRITE N12-WHEN-N12P))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(GET-RD-OF-ASM-JALR-GL
 (3 3 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(GET-RD-OF-ASM-JALR
 (87 36 (:REWRITE DEFAULT-+-2))
 (63 36 (:REWRITE DEFAULT-+-1))
 (37 34 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE N05-WHEN-N05P))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (16 2 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (16 2 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (16 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (16 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (14 14 (:REWRITE N12-WHEN-N12P))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
