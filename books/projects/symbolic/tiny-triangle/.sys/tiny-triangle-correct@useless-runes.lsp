(|idx|
 (13 13 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE NATP-RW))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TRI
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE NATP-RW))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(TINY-TRI-CUTPOINT)
(TINY-TRI-ASSERTION
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(DUMMY-TINY-STATE)
(TINY-TRI-EXITPOINT)
(TINY-TRI-PRECONDITION)
(TINY-TRI-POSTCONDITION)
(PLUS<32>-IS-SIGNED-BYTE
 (109 11 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (93 8 (:DEFINITION UNSIGNED-BYTE-P))
 (50 4 (:REWRITE LOGEXT-IDENTITY))
 (33 3 (:LINEAR LOGEXT-BOUNDS))
 (24 5 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (23 22 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:META CANCEL_PLUS-LESSP-CORRECT))
 (17 17 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (11 11 (:TYPE-PRESCRIPTION LOGEXT-TYPE))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (10 3 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (8 8 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (7 1 (:REWRITE +BV32-SIMPLE))
 (5 5 (:REWRITE LESS-NEG-CONST))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(IDX-IS-SIGNED-BYTE-P
 (193 15 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (169 12 (:DEFINITION UNSIGNED-BYTE-P))
 (54 4 (:REWRITE LOGEXT-IDENTITY))
 (50 47 (:REWRITE DEFAULT-<-1))
 (47 47 (:REWRITE DEFAULT-<-2))
 (47 47 (:META CANCEL_PLUS-LESSP-CORRECT))
 (33 3 (:LINEAR LOGEXT-BOUNDS))
 (32 9 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (27 27 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (21 21 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (18 3 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (14 7 (:REWRITE NATP-RW))
 (11 11 (:TYPE-PRESCRIPTION LOGEXT-TYPE))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (9 9 (:REWRITE LESS-NEG-CONST))
 (8 1 (:REWRITE +BV32-SIMPLE))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 )
(TRI-IS-SIGNED-BYTE-P
 (510 6 (:DEFINITION |idx|))
 (412 10 (:REWRITE LOGEXT-IDENTITY))
 (363 21 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (327 18 (:DEFINITION UNSIGNED-BYTE-P))
 (174 174 (:TYPE-PRESCRIPTION |idx|))
 (85 76 (:REWRITE DEFAULT-<-1))
 (76 76 (:REWRITE DEFAULT-<-2))
 (76 76 (:META CANCEL_PLUS-LESSP-CORRECT))
 (74 74 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (74 14 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (70 14 (:REWRITE INTEGERP-+))
 (44 15 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (43 36 (:REWRITE DEFAULT-+-2))
 (42 36 (:REWRITE DEFAULT-+-1))
 (35 7 (:REWRITE +BV32-SIMPLE))
 (33 3 (:LINEAR LOGEXT-BOUNDS))
 (27 27 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (24 24 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (24 12 (:DEFINITION FIX))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (18 3 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (15 15 (:REWRITE LESS-NEG-CONST))
 (14 7 (:REWRITE NATP-RW))
 (11 11 (:TYPE-PRESCRIPTION LOGEXT-TYPE))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 )
(SIGNED-BYTE-P-PLUS
 (27 4 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (20 3 (:DEFINITION UNSIGNED-BYTE-P))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (4 1 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (3 3 (:REWRITE LESS-NEG-CONST))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 )
(TINY-TRI-MEASURE
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(L1
 (101 4 (:REWRITE O-INFP-O-FINP-O<=))
 (78 2 (:REWRITE O-FIRST-EXPT-<))
 (69 6 (:REWRITE LEN>0-CONSP))
 (56 4 (:REWRITE O<=-O-FINP-DEF))
 (54 3 (:REWRITE O-INFP-O+-3))
 (45 3 (:REWRITE O+-O-FIRST-EXPT-SMASH))
 (42 1 (:REWRITE |a <= b & c <= d  =>  a+c <= b+d|))
 (40 2 (:REWRITE |(a <= b) & (c <= d)  =>  ac <= bd|))
 (39 3 (:DEFINITION LEN))
 (38 1 (:REWRITE |a <= b & c < d  =>  a+c < b+d|))
 (33 4 (:REWRITE O-FINP-<))
 (30 6 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (28 2 (:REWRITE O+-O-FIRST-COEFF-3))
 (27 27 (:TYPE-PRESCRIPTION LEN))
 (25 1 (:REWRITE |(a <= b) & (c < d)  =>  ac < bd|))
 (18 3 (:REWRITE OMEGA-O<))
 (14 7 (:REWRITE NATP-RW))
 (12 6 (:REWRITE O-INFP-O*-2))
 (12 4 (:REWRITE O*-O-FIRST-EXPT-SMASH-2))
 (9 6 (:REWRITE DEFAULT-<-2))
 (9 3 (:REWRITE O-INFP-O+-2))
 (8 4 (:REWRITE O*-O-FINP))
 (7 7 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (7 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE |a < b & b < c  =>  a < c|))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(TINY-TRI-RUN
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(DEFAULT-NOT-CUTPOINT)
(PRE-IMPLIES-CUTPOINT
 (76 38 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (38 38 (:TYPE-PRESCRIPTION MEMP))
 )
(EXITPOINT-IS-CUTPOINT
 (18 9 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (9 9 (:TYPE-PRESCRIPTION MEMP))
 )
(PRE-IMPLIES-ASSERTION
 (221 24 (:REWRITE NTH-WITH-LARGE-INDEX))
 (112 2 (:REWRITE MEMP-TRUE-LISTP))
 (109 35 (:REWRITE DEFAULT-CDR))
 (82 9 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (75 1 (:DEFINITION TRUE-LISTP))
 (58 29 (:REWRITE DEFAULT-+-2))
 (36 4 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (34 30 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (33 28 (:REWRITE DEFAULT-<-2))
 (30 28 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE DEFAULT-+-1))
 (28 28 (:META CANCEL_PLUS-LESSP-CORRECT))
 (22 1 (:REWRITE ARB-MEMORY))
 (19 5 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE PROG-LOOKUP))
 (16 2 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (13 13 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (12 12 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (11 11 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (4 4 (:REWRITE LESS-NEG-CONST))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(ASSERTION-IMPLIES-POST
 (100 62 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (38 38 (:TYPE-PRESCRIPTION MEMP))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-test|)
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-base|)
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-stn|))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-DEF|)
(CONCRETE-STEPS-TO-CUTPOINT-TAIL)
(CONCRETE-STEPS-TO-CUTPOINT-TAIL-DEF
 (4215 39 (:LINEAR MEMI-ELEMENTS-LEQ))
 (3556 52 (:DEFINITION MEMP))
 (2323 1166 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (2242 147 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1722 101 (:DEFINITION INTEGER-RANGE-P))
 (1681 200 (:REWRITE LEN>0-CONSP))
 (1595 127 (:DEFINITION LEN))
 (1465 2 (:REWRITE NEXT-INSTR-HALT))
 (1416 1416 (:TYPE-PRESCRIPTION MEMP))
 (1104 52 (:DEFINITION SIGNED-BYTE-P))
 (960 101 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (916 28 (:DEFINITION MEMI))
 (875 101 (:DEFINITION UNSIGNED-BYTE-P))
 (598 1 (:REWRITE PRE-IMPLIES-CUTPOINT))
 (596 1 (:DEFINITION TINY-TRI-PRECONDITION))
 (579 12 (:REWRITE ARB-MEMORY))
 (561 387 (:REWRITE DEFAULT-<-2))
 (538 2 (:REWRITE NEXT-INSTR-SUB))
 (538 2 (:REWRITE NEXT-INSTR-RETURN))
 (538 2 (:REWRITE NEXT-INSTR-PUSHSI))
 (538 2 (:REWRITE NEXT-INSTR-PUSHS))
 (538 2 (:REWRITE NEXT-INSTR-JUMPZ))
 (538 2 (:REWRITE NEXT-INSTR-JUMP))
 (538 2 (:REWRITE NEXT-INSTR-DUP))
 (538 2 (:REWRITE NEXT-INSTR-CALL))
 (538 2 (:REWRITE NEXT-INSTR-ADD))
 (441 49 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (440 1 (:DEFINITION TINY-STATEP))
 (410 387 (:REWRITE DEFAULT-<-1))
 (390 6 (:DEFINITION NFIX))
 (387 387 (:META CANCEL_PLUS-LESSP-CORRECT))
 (258 129 (:REWRITE DEFAULT-+-2))
 (223 189 (:REWRITE DEFAULT-CDR))
 (222 4 (:REWRITE NATP-RW))
 (178 178 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (147 147 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (129 129 (:REWRITE DEFAULT-+-1))
 (112 2 (:REWRITE MEMP-TRUE-LISTP))
 (109 109 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (107 107 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (107 107 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (78 1 (:DEFINITION TRUE-LISTP))
 (67 61 (:REWRITE DEFAULT-CAR))
 (66 2 (:REWRITE NEXT-INSTR-POP))
 (56 2 (:DEFINITION DTOS-VAL))
 (49 49 (:REWRITE LESS-NEG-CONST))
 (42 1 (:REWRITE EXITPOINT-IS-CUTPOINT))
 (42 1 (:DEFINITION PROGCP))
 (42 1 (:DEFINITION DTOSP))
 (42 1 (:DEFINITION CTOSP))
 (40 1 (:DEFINITION TINY-TRI-EXITPOINT))
 (38 29 (:REWRITE PROG-LOOKUP))
 (36 36 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (36 36 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (20 20 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (16 1 (:DEFINITION LENGTH))
 (15 3 (:DEFINITION DTOS))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION PROGRAM-LOADED))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:TYPE-PRESCRIPTION TINY-TRI-PRECONDITION))
 (1 1 (:TYPE-PRESCRIPTION TINY-TRI-EXITPOINT))
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 )
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-defpun-test|)
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-defpun-base|)
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 )
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-defpun-stn|))
 )
(|TINY-TRI-PARTIAL-EXITSTEPS-TAIL-arity-1-DEF|)
(TINY-TRI-PARTIAL-EXITSTEPS-TAIL)
(TINY-TRI-PARTIAL-EXITSTEPS-TAIL-DEF
 (2090 19 (:LINEAR MEMI-ELEMENTS-LEQ))
 (1659 23 (:DEFINITION MEMP))
 (1110 555 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (1015 59 (:REWRITE NTH-WITH-LARGE-INDEX))
 (761 75 (:REWRITE LEN>0-CONSP))
 (758 46 (:DEFINITION INTEGER-RANGE-P))
 (745 1 (:REWRITE NEXT-INSTR-HALT))
 (688 52 (:DEFINITION LEN))
 (670 670 (:TYPE-PRESCRIPTION MEMP))
 (517 23 (:DEFINITION SIGNED-BYTE-P))
 (448 46 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (433 13 (:DEFINITION MEMI))
 (356 46 (:DEFINITION UNSIGNED-BYTE-P))
 (269 1 (:REWRITE NEXT-INSTR-SUB))
 (269 1 (:REWRITE NEXT-INSTR-RETURN))
 (269 1 (:REWRITE NEXT-INSTR-PUSHSI))
 (269 1 (:REWRITE NEXT-INSTR-PUSHS))
 (269 1 (:REWRITE NEXT-INSTR-JUMPZ))
 (269 1 (:REWRITE NEXT-INSTR-JUMP))
 (269 1 (:REWRITE NEXT-INSTR-DUP))
 (269 1 (:REWRITE NEXT-INSTR-CALL))
 (269 1 (:REWRITE NEXT-INSTR-ADD))
 (259 178 (:REWRITE DEFAULT-<-2))
 (252 4 (:REWRITE ARB-MEMORY))
 (207 23 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (195 3 (:DEFINITION NFIX))
 (184 178 (:REWRITE DEFAULT-<-1))
 (178 178 (:META CANCEL_PLUS-LESSP-CORRECT))
 (111 2 (:REWRITE NATP-RW))
 (106 53 (:REWRITE DEFAULT-+-2))
 (84 84 (:REWRITE DEFAULT-CDR))
 (81 81 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (69 69 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (53 53 (:REWRITE DEFAULT-+-1))
 (50 50 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (46 46 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (46 46 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (33 1 (:REWRITE NEXT-INSTR-POP))
 (32 32 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE LESS-NEG-CONST))
 (13 13 (:REWRITE PROG-LOOKUP))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CONCRETE-STEPS-TO-CUTPOINT
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(CONCRETE-NEXTT-CUTPOINT
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (6 6 (:TYPE-PRESCRIPTION TINY-TRI-RUN))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(NEXTT-CUTPOINT-FOR-CUTPOINT)
(NEXTT-CUTPOINT-FOR-NOT-CUTPOINT)
(ASSERTION-INVARIANT-OVER-CUTPOINTS
 (2803 699 (:REWRITE DEFAULT-CDR))
 (2598 544 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1461 764 (:REWRITE DEFAULT-+-2))
 (781 764 (:REWRITE DEFAULT-+-1))
 (699 679 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (603 23 (:REWRITE NEXT-INSTR-HALT))
 (536 10 (:REWRITE MEMP-TRUE-LISTP))
 (347 5 (:DEFINITION TRUE-LISTP))
 (328 289 (:REWRITE DEFAULT-<-2))
 (321 22 (:REWRITE +BV32-SIMPLE))
 (309 289 (:REWRITE DEFAULT-<-1))
 (237 19 (:REWRITE NEXT-INSTR-RETURN))
 (237 19 (:REWRITE NEXT-INSTR-CALL))
 (199 35 (:REWRITE INTEGERP-+))
 (188 188 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (181 14 (:LINEAR LOGEXT-BOUNDS))
 (132 32 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (92 16 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (90 24 (:REWRITE DEFAULT-CAR))
 (79 79 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (75 75 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (70 70 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (70 70 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (60 60 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (44 44 (:REWRITE LESS-NEG-CONST))
 (33 3 (:REWRITE INTEGERP-UNARY--))
 (27 27 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (26 20 (:REWRITE O-INFP->NEQ-0))
 (23 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 1 (:REWRITE NATP-POSP--1))
 (17 1 (:REWRITE NATP-POSP))
 (2 2 (:TYPE-PRESCRIPTION O-FINP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(TINY-TRI-PARTIAL-EXITSTEPS
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(NEXT-PARTIAL-CORRECTNESS)
(DEFAULT-NOT-CUTPOINT)
(PRE-IMPLIES-CUTPOINT
 (76 38 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (38 38 (:TYPE-PRESCRIPTION MEMP))
 )
(EXITPOINT-IS-CUTPOINT
 (18 9 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (9 9 (:TYPE-PRESCRIPTION MEMP))
 )
(PRE-IMPLIES-ASSERTION
 (221 24 (:REWRITE NTH-WITH-LARGE-INDEX))
 (112 2 (:REWRITE MEMP-TRUE-LISTP))
 (109 35 (:REWRITE DEFAULT-CDR))
 (82 9 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (75 1 (:DEFINITION TRUE-LISTP))
 (58 29 (:REWRITE DEFAULT-+-2))
 (36 4 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (34 30 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (33 28 (:REWRITE DEFAULT-<-2))
 (30 28 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE DEFAULT-+-1))
 (28 28 (:META CANCEL_PLUS-LESSP-CORRECT))
 (22 1 (:REWRITE ARB-MEMORY))
 (19 5 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE PROG-LOOKUP))
 (16 2 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (13 13 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (12 12 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (11 11 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (4 4 (:REWRITE LESS-NEG-CONST))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(ASSERTION-IMPLIES-POST
 (100 62 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (38 38 (:TYPE-PRESCRIPTION MEMP))
 )
(MEASURE-IS-ORDINAL
 (2240 58 (:REWRITE NTH-WITH-LARGE-INDEX))
 (2022 34 (:DEFINITION MEMP))
 (1910 92 (:REWRITE ARB-MEMORY))
 (1306 134 (:REWRITE LEN>0-CONSP))
 (1264 96 (:DEFINITION LEN))
 (981 117 (:REWRITE DEFAULT-+-2))
 (964 68 (:DEFINITION INTEGER-RANGE-P))
 (786 312 (:REWRITE DEFAULT-<-2))
 (686 34 (:DEFINITION SIGNED-BYTE-P))
 (584 68 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (537 312 (:REWRITE DEFAULT-<-1))
 (513 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (475 95 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (448 68 (:DEFINITION UNSIGNED-BYTE-P))
 (440 4 (:LINEAR MEMI-ELEMENTS-LEQ))
 (313 313 (:META CANCEL_PLUS-LESSP-CORRECT))
 (306 34 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (264 4 (:REWRITE O+-O-FIRST-EXPT-SMASH))
 (239 39 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (186 117 (:REWRITE DEFAULT-+-1))
 (142 142 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (134 13 (:REWRITE INTEGERP-+))
 (130 130 (:REWRITE DEFAULT-CDR))
 (126 126 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (102 102 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (98 8 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (92 4 (:REWRITE O*-O-FIRST-EXPT))
 (68 68 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (68 68 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (56 8 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (46 6 (:REWRITE INTEGERP-UNARY--))
 (46 6 (:REWRITE INTEGERP--))
 (36 6 (:REWRITE O-FIRST-EXPT-<))
 (34 34 (:REWRITE LESS-NEG-CONST))
 (34 34 (:REWRITE DEFAULT-CAR))
 (18 6 (:REWRITE O-FINP-<))
 (18 6 (:REWRITE AC-<))
 (12 12 (:REWRITE PROG-LOOKUP))
 (12 4 (:REWRITE O-INFP->NEQ-0))
 (12 4 (:REWRITE O*-O-FIRST-EXPT-SMASH-2))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 4 (:REWRITE O*-O-FINP))
 (6 6 (:REWRITE |a < b & b < c  =>  a < c|))
 (6 6 (:REWRITE O-FIRST-COEFF-<))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-test|)
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-base|)
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-defpun-stn|))
 )
(|CONCRETE-STEPS-TO-CUTPOINT-TAIL-arity-1-DEF|)
(CONCRETE-STEPS-TO-CUTPOINT-TAIL)
(CONCRETE-STEPS-TO-CUTPOINT-TAIL-DEF
 (4215 39 (:LINEAR MEMI-ELEMENTS-LEQ))
 (3556 52 (:DEFINITION MEMP))
 (2323 1166 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (2242 147 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1722 101 (:DEFINITION INTEGER-RANGE-P))
 (1681 200 (:REWRITE LEN>0-CONSP))
 (1595 127 (:DEFINITION LEN))
 (1465 2 (:REWRITE NEXT-INSTR-HALT))
 (1416 1416 (:TYPE-PRESCRIPTION MEMP))
 (1104 52 (:DEFINITION SIGNED-BYTE-P))
 (960 101 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (916 28 (:DEFINITION MEMI))
 (875 101 (:DEFINITION UNSIGNED-BYTE-P))
 (598 1 (:REWRITE PRE-IMPLIES-CUTPOINT))
 (596 1 (:DEFINITION TINY-TRI-PRECONDITION))
 (579 12 (:REWRITE ARB-MEMORY))
 (561 387 (:REWRITE DEFAULT-<-2))
 (538 2 (:REWRITE NEXT-INSTR-SUB))
 (538 2 (:REWRITE NEXT-INSTR-RETURN))
 (538 2 (:REWRITE NEXT-INSTR-PUSHSI))
 (538 2 (:REWRITE NEXT-INSTR-PUSHS))
 (538 2 (:REWRITE NEXT-INSTR-JUMPZ))
 (538 2 (:REWRITE NEXT-INSTR-JUMP))
 (538 2 (:REWRITE NEXT-INSTR-DUP))
 (538 2 (:REWRITE NEXT-INSTR-CALL))
 (538 2 (:REWRITE NEXT-INSTR-ADD))
 (441 49 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (440 1 (:DEFINITION TINY-STATEP))
 (410 387 (:REWRITE DEFAULT-<-1))
 (390 6 (:DEFINITION NFIX))
 (387 387 (:META CANCEL_PLUS-LESSP-CORRECT))
 (258 129 (:REWRITE DEFAULT-+-2))
 (223 189 (:REWRITE DEFAULT-CDR))
 (222 4 (:REWRITE NATP-RW))
 (178 178 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (147 147 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (129 129 (:REWRITE DEFAULT-+-1))
 (112 2 (:REWRITE MEMP-TRUE-LISTP))
 (109 109 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (107 107 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (107 107 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (78 1 (:DEFINITION TRUE-LISTP))
 (67 61 (:REWRITE DEFAULT-CAR))
 (66 2 (:REWRITE NEXT-INSTR-POP))
 (56 2 (:DEFINITION DTOS-VAL))
 (49 49 (:REWRITE LESS-NEG-CONST))
 (42 1 (:REWRITE EXITPOINT-IS-CUTPOINT))
 (42 1 (:DEFINITION PROGCP))
 (42 1 (:DEFINITION DTOSP))
 (42 1 (:DEFINITION CTOSP))
 (40 1 (:DEFINITION TINY-TRI-EXITPOINT))
 (38 29 (:REWRITE PROG-LOOKUP))
 (36 36 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (36 36 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (20 20 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (16 1 (:DEFINITION LENGTH))
 (15 3 (:DEFINITION DTOS))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION PROGRAM-LOADED))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:TYPE-PRESCRIPTION TINY-TRI-PRECONDITION))
 (1 1 (:TYPE-PRESCRIPTION TINY-TRI-EXITPOINT))
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 )
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-defpun-test|)
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-defpun-base|)
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 )
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1|
 (1 1 (:TYPE-PRESCRIPTION |TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-defpun-stn|))
 )
(|TINY-TRI-TOTAL-EXITSTEPS-TAIL-arity-1-DEF|)
(TINY-TRI-TOTAL-EXITSTEPS-TAIL)
(TINY-TRI-TOTAL-EXITSTEPS-TAIL-DEF
 (2090 19 (:LINEAR MEMI-ELEMENTS-LEQ))
 (1659 23 (:DEFINITION MEMP))
 (1110 555 (:TYPE-PRESCRIPTION MEMP-NTH-INTEGERP))
 (1015 59 (:REWRITE NTH-WITH-LARGE-INDEX))
 (761 75 (:REWRITE LEN>0-CONSP))
 (758 46 (:DEFINITION INTEGER-RANGE-P))
 (745 1 (:REWRITE NEXT-INSTR-HALT))
 (688 52 (:DEFINITION LEN))
 (670 670 (:TYPE-PRESCRIPTION MEMP))
 (517 23 (:DEFINITION SIGNED-BYTE-P))
 (448 46 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (433 13 (:DEFINITION MEMI))
 (356 46 (:DEFINITION UNSIGNED-BYTE-P))
 (269 1 (:REWRITE NEXT-INSTR-SUB))
 (269 1 (:REWRITE NEXT-INSTR-RETURN))
 (269 1 (:REWRITE NEXT-INSTR-PUSHSI))
 (269 1 (:REWRITE NEXT-INSTR-PUSHS))
 (269 1 (:REWRITE NEXT-INSTR-JUMPZ))
 (269 1 (:REWRITE NEXT-INSTR-JUMP))
 (269 1 (:REWRITE NEXT-INSTR-DUP))
 (269 1 (:REWRITE NEXT-INSTR-CALL))
 (269 1 (:REWRITE NEXT-INSTR-ADD))
 (259 178 (:REWRITE DEFAULT-<-2))
 (252 4 (:REWRITE ARB-MEMORY))
 (207 23 (:REWRITE SIGNED-BYTE-P-32-BOUNDS))
 (195 3 (:DEFINITION NFIX))
 (184 178 (:REWRITE DEFAULT-<-1))
 (178 178 (:META CANCEL_PLUS-LESSP-CORRECT))
 (111 2 (:REWRITE NATP-RW))
 (106 53 (:REWRITE DEFAULT-+-2))
 (84 84 (:REWRITE DEFAULT-CDR))
 (81 81 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (69 69 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (53 53 (:REWRITE DEFAULT-+-1))
 (50 50 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (46 46 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (46 46 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (33 1 (:REWRITE NEXT-INSTR-POP))
 (32 32 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE LESS-NEG-CONST))
 (13 13 (:REWRITE PROG-LOOKUP))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION NEXT))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CONCRETE-STEPS-TO-CUTPOINT
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(CONCRETE-NEXTT-CUTPOINT
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (6 6 (:TYPE-PRESCRIPTION TINY-TRI-RUN))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(NEXTT-CUTPOINT-FOR-CUTPOINT)
(NEXTT-CUTPOINT-FOR-NOT-CUTPOINT)
(TOTAL-CORRECTNESS-PROOF-OBLIGATION
 (5020 1083 (:REWRITE NTH-WITH-LARGE-INDEX))
 (3869 978 (:REWRITE DEFAULT-CDR))
 (2070 1100 (:REWRITE DEFAULT-+-2))
 (1482 80 (:REWRITE NEXT-INSTR-HALT))
 (1131 1100 (:REWRITE DEFAULT-+-1))
 (1032 954 (:TYPE-PRESCRIPTION TYPSET-LEN-ZERO))
 (936 18 (:REWRITE MEMP-TRUE-LISTP))
 (724 44 (:REWRITE +BV32-SIMPLE))
 (623 66 (:REWRITE NEXT-INSTR-RETURN))
 (623 66 (:REWRITE NEXT-INSTR-CALL))
 (591 9 (:DEFINITION TRUE-LISTP))
 (580 514 (:REWRITE DEFAULT-<-2))
 (545 514 (:REWRITE DEFAULT-<-1))
 (331 331 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (331 331 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (319 59 (:REWRITE INTEGERP-+))
 (313 19 (:REWRITE O-FIRST-EXPT-<))
 (312 312 (:REWRITE NTH-UPDATE-ADDR-INTEGERP))
 (296 22 (:LINEAR LOGEXT-BOUNDS))
 (236 56 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (236 5 (:REWRITE O+-O-FIRST-EXPT-SMASH))
 (222 5 (:REWRITE O+-ATOM-DEF))
 (188 27 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (165 19 (:REWRITE O-FIRST-COEFF-<))
 (154 40 (:REWRITE DEFAULT-CAR))
 (152 139 (:REWRITE O-INFP->NEQ-0))
 (140 20 (:REWRITE FALSIFY-SIGNED-BYTE-P))
 (140 12 (:REWRITE O*-O-FIRST-EXPT))
 (119 119 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (114 1 (:REWRITE O-FIRST-EXPT-<-O+))
 (113 113 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (88 88 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (81 2 (:REWRITE O+-O-FIRST-EXPT-2))
 (78 78 (:REWRITE LESS-NEG-CONST))
 (69 7 (:REWRITE O-FIRST-EXPT-O-INFP))
 (61 2 (:REWRITE O+-O-FIRST-EXPT-1))
 (57 19 (:REWRITE AC-<))
 (56 19 (:REWRITE O-FINP-<))
 (54 54 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (50 10 (:TYPE-PRESCRIPTION O+-O-FINP))
 (43 1 (:REWRITE O-INFP-O+))
 (33 3 (:REWRITE INTEGERP-UNARY--))
 (28 1 (:REWRITE |a <= b & c <= d  =>  a+c <= b+d|))
 (28 1 (:REWRITE O-INFP-O+-3))
 (27 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 21 (:REWRITE |a < b & b < c  =>  a < c|))
 (21 7 (:REWRITE O*-O-FIRST-EXPT-SMASH-2))
 (19 19 (:TYPE-PRESCRIPTION TINY-TRI-MEASURE))
 (18 5 (:REWRITE O-INFP-O-FINP-O<=))
 (18 1 (:REWRITE NATP-POSP--1))
 (17 1 (:REWRITE NATP-POSP))
 (14 7 (:REWRITE O*-O-FINP))
 (10 10 (:TYPE-PRESCRIPTION OB+))
 (9 2 (:REWRITE |~(a<0)|))
 (7 1 (:REWRITE |0 < a  =  ~(a = 0)|))
 (6 1 (:REWRITE O-INFP-O*))
 (4 2 (:REWRITE O-FIRST-EXPT-O-P))
 (4 1 (:REWRITE EQUAL-CONSTANT-+))
 (2 1 (:REWRITE O-INFP-O+-2))
 (2 1 (:REWRITE O-INFP-O*-2))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE OMEGA-O-FIRST-EXPT))
 )
(ASSERTION-INVARIANT-OVER-CUTPOINTS)
(NEXTT-CUTPOINT-IS-CUTPOINT)
(CUTPOINT-MEASURE-DECREASES)
(SOME-CUTPOINT-IS-REACHABLE)
(TINY-TRI-TOTAL-EXITSTEPS
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(NEXT-TOTAL-CORRECTNESS)
