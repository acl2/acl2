(UNHIDE
 (1 1 (:TYPE-PRESCRIPTION UNHIDE))
 )
(UNHIDE-UNHIDDEN
 (3 3 (:TYPE-PRESCRIPTION UNHIDE))
 )
(UNHIDE-HIDE
 (3 3 (:TYPE-PRESCRIPTION UNHIDE))
 )
(FIX-LIST)
(PAIRLIS$-FIX-LIST
 (26 26 (:TYPE-PRESCRIPTION FIX-LIST))
 )
(QUOTE-LIST)
(APPLY-FOR-DEFEVALUATOR)
(UNHIDE-EVAL)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(UNHIDE-EVAL-CONSTRAINT-0)
(UNHIDE-EVAL-CONSTRAINT-1)
(UNHIDE-EVAL-CONSTRAINT-2)
(UNHIDE-EVAL-CONSTRAINT-3)
(UNHIDE-EVAL-CONSTRAINT-4)
(UNHIDE-EVAL-CONSTRAINT-5)
(UNHIDE-EVAL-CONSTRAINT-6)
(UNHIDE-EVAL-CONSTRAINT-7)
(UNHIDE-EVAL-CONSTRAINT-8)
(UNHIDE-EVAL-CONSTRAINT-9)
(PSEUDO-TERMP-KEY)
(NARY-BETA-REDUCE
 (396 195 (:REWRITE DEFAULT-+-2))
 (338 325 (:REWRITE DEFAULT-CDR))
 (257 195 (:REWRITE DEFAULT-+-1))
 (175 35 (:DEFINITION LEN))
 (160 40 (:REWRITE COMMUTATIVITY-OF-+))
 (160 40 (:DEFINITION INTEGER-ABS))
 (160 20 (:DEFINITION LENGTH))
 (62 50 (:REWRITE DEFAULT-<-2))
 (58 50 (:REWRITE DEFAULT-<-1))
 (55 55 (:TYPE-PRESCRIPTION LEN))
 (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (37 37 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (29 29 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (20 20 (:REWRITE DEFAULT-REALPART))
 (20 20 (:REWRITE DEFAULT-NUMERATOR))
 (20 20 (:REWRITE DEFAULT-IMAGPART))
 (20 20 (:REWRITE DEFAULT-DENOMINATOR))
 (20 20 (:REWRITE DEFAULT-COERCE-2))
 (20 20 (:REWRITE DEFAULT-COERCE-1))
 (15 5 (:DEFINITION SYMBOL-LISTP))
 (6 6 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(UNHIDE-EVAL-KEY
 (143 70 (:REWRITE DEFAULT-+-2))
 (97 70 (:REWRITE DEFAULT-+-1))
 (64 16 (:REWRITE COMMUTATIVITY-OF-+))
 (64 16 (:DEFINITION INTEGER-ABS))
 (64 8 (:DEFINITION LENGTH))
 (40 8 (:DEFINITION LEN))
 (25 20 (:REWRITE DEFAULT-<-2))
 (24 20 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE DEFAULT-CDR))
 (19 19 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(UNHIDE-EVAL-KEY-REDUCTION
 (53 43 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (53 43 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (30 6 (:DEFINITION ASSOC-EQUAL))
 )
(WF-BETA-TERM
 (366 180 (:REWRITE DEFAULT-+-2))
 (242 180 (:REWRITE DEFAULT-+-1))
 (160 40 (:REWRITE COMMUTATIVITY-OF-+))
 (160 40 (:DEFINITION INTEGER-ABS))
 (160 20 (:DEFINITION LENGTH))
 (100 20 (:DEFINITION LEN))
 (62 50 (:REWRITE DEFAULT-<-2))
 (58 50 (:REWRITE DEFAULT-<-1))
 (54 54 (:REWRITE DEFAULT-CDR))
 (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 20 (:TYPE-PRESCRIPTION LEN))
 (20 20 (:REWRITE DEFAULT-REALPART))
 (20 20 (:REWRITE DEFAULT-NUMERATOR))
 (20 20 (:REWRITE DEFAULT-IMAGPART))
 (20 20 (:REWRITE DEFAULT-DENOMINATOR))
 (20 20 (:REWRITE DEFAULT-COERCE-2))
 (20 20 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(APPEND-NIL-FIX
 (48 6 (:REWRITE APPEND-TO-NIL))
 (32 7 (:DEFINITION TRUE-LISTP))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 12 (:REWRITE DEFAULT-CDR))
 (7 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-1))
 )
(LATE-BINDING-REDUCTION
 (136 127 (:REWRITE DEFAULT-CAR))
 (102 97 (:REWRITE DEFAULT-CDR))
 (56 28 (:REWRITE DEFAULT-+-2))
 (28 28 (:REWRITE DEFAULT-+-1))
 (23 23 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (23 23 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (23 23 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (23 23 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (8 8 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 )
(ASSOC-EQ-PAIRLIS$-NON-MEMBER
 (28 27 (:REWRITE DEFAULT-CAR))
 (15 14 (:REWRITE DEFAULT-CDR))
 )
(CAR-QUOTE-LIST
 (22 12 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(CAR-UNHIDE-EVAL-LIST
 (5 5 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-1))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(CONSP-UNHIDE-EVAL-LIST
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-1))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(UNHIDE-EVAL-KEY-NARY-BETA-REDUCE
 (265 21 (:DEFINITION PAIRLIS$))
 (229 225 (:REWRITE DEFAULT-CAR))
 (203 181 (:REWRITE DEFAULT-CDR))
 (176 22 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (68 34 (:REWRITE DEFAULT-+-2))
 (34 34 (:REWRITE DEFAULT-+-1))
 (26 2 (:DEFINITION KWOTE-LST))
 (24 24 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 (21 3 (:DEFINITION ASSOC-EQUAL))
 (15 15 (:TYPE-PRESCRIPTION KWOTE-LST))
 (6 6 (:TYPE-PRESCRIPTION PAIRLIS$))
 (2 2 (:DEFINITION KWOTE))
 )
(PARA-LAMBDA-EXPR-P
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (7 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(PARA-MAP-LAMBDA-P)
(PARA-LAMBDA-EXPR-KEY-P)
(UNHIDE-EVAL-KEY-LAMBDA-EXPR
 (203 203 (:REWRITE DEFAULT-CAR))
 (167 157 (:REWRITE DEFAULT-CDR))
 (120 10 (:DEFINITION PAIRLIS$))
 (72 36 (:REWRITE DEFAULT-+-2))
 (70 10 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (36 36 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (16 16 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (14 14 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (14 14 (:REWRITE UNHIDE-EVAL-CONSTRAINT-1))
 (10 10 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 )
(LAMBDA-EXPR-P)
(LAMBDA-EXPR-P-TO-PARA-LAMBDA-EXPR-KEY-P
 (22 22 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-+-1))
 )
(UNHIDE-EVAL-LAMBDA-EXPR-HELPER
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (10 2 (:DEFINITION PAIRLIS$))
 )
(UNHIDE-EVAL-LAMBDA-EXPR
 (12 1 (:DEFINITION PAIRLIS$))
 (7 6 (:REWRITE DEFAULT-CDR))
 (7 1 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (6 6 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE UNHIDE-EVAL-KEY-LAMBDA-EXPR))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-1))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-5))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 (1 1 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 )
(PSEUDO-TERMP-KEY-IMPLIES-WF-BETA-TERM
 (142 142 (:REWRITE DEFAULT-CAR))
 (113 113 (:REWRITE DEFAULT-CDR))
 (90 18 (:DEFINITION LEN))
 (42 42 (:TYPE-PRESCRIPTION LEN))
 (39 39 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (36 18 (:REWRITE DEFAULT-+-2))
 (34 34 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (12 6 (:DEFINITION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(UNHIDE-EVAL-NARY-BETA-REDUCE
 (272 5 (:REWRITE PSEUDO-TERMP-KEY-IMPLIES-WF-BETA-TERM))
 (262 5 (:DEFINITION PSEUDO-TERMP-KEY))
 (225 3 (:DEFINITION PSEUDO-TERMP))
 (63 63 (:REWRITE DEFAULT-CAR))
 (62 61 (:REWRITE DEFAULT-CDR))
 (31 1 (:DEFINITION NARY-BETA-REDUCE))
 (22 11 (:REWRITE DEFAULT-+-2))
 (22 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (21 21 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (20 2 (:DEFINITION PAIRLIS$))
 (18 3 (:DEFINITION SYMBOL-LISTP))
 (17 17 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (15 15 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (15 3 (:DEFINITION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (11 11 (:REWRITE DEFAULT-+-1))
 (10 1 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (9 3 (:REWRITE UNHIDE-EVAL-LAMBDA-EXPR))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 7 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (7 1 (:DEFINITION ASSOC-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION LAMBDA-EXPR-P))
 (5 5 (:TYPE-PRESCRIPTION PSEUDO-TERMP-KEY))
 (3 3 (:REWRITE UNHIDE-EVAL-KEY-LAMBDA-EXPR))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (3 3 (:REWRITE UNHIDE-EVAL-CONSTRAINT-1))
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION PAIRLIS$))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-5))
 (1 1 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 (1 1 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 (1 1 (:REWRITE ASSOC-EQ-PAIRLIS$-NON-MEMBER))
 )
(UNIDE-EVAL-TO-NARY-BETA-REDUCE
 (36 18 (:REWRITE DEFAULT-+-2))
 (20 2 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (18 18 (:REWRITE DEFAULT-+-1))
 (15 4 (:DEFINITION SYMBOL-LISTP))
 (11 11 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (11 11 (:REWRITE UNHIDE-EVAL-CONSTRAINT-8))
 (11 11 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (11 11 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 1 (:DEFINITION ASSOC-EQUAL))
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION PAIRLIS$))
 (2 2 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE ASSOC-EQ-PAIRLIS$-NON-MEMBER))
 )
(NARY-BETA-REDUCE-LAMBDA
 (160 160 (:REWRITE DEFAULT-CDR))
 (148 148 (:REWRITE DEFAULT-CAR))
 (104 52 (:REWRITE DEFAULT-+-2))
 (52 52 (:REWRITE DEFAULT-+-1))
 (27 9 (:DEFINITION SYMBOL-LISTP))
 (19 19 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 12 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 )
(UNHIDE-P)
(HIDE-P)
(NARY-BETA-REDUCE-HIDE-WRAPPER
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION NARY-BETA-REDUCE-HIDE-WRAPPER))
 )
(NARY-*META*-BETA-REDUCE-HIDE
 (58 29 (:REWRITE DEFAULT-+-2))
 (46 4 (:DEFINITION PAIRLIS$))
 (29 29 (:REWRITE DEFAULT-+-1))
 (26 2 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (25 20 (:REWRITE UNHIDE-EVAL-CONSTRAINT-9))
 (24 6 (:DEFINITION SYMBOL-LISTP))
 (17 17 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 12 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (15 12 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (14 2 (:DEFINITION ASSOC-EQUAL))
 (11 11 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION PAIRLIS$))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-5))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 (2 2 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 (2 2 (:REWRITE ASSOC-EQ-PAIRLIS$-NON-MEMBER))
 )
(NARY-UNHIDE-HIDE-WRAPPER
 (51 51 (:REWRITE DEFAULT-CDR))
 (41 41 (:REWRITE DEFAULT-CAR))
 (30 6 (:DEFINITION LEN))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (12 6 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 2 (:DEFINITION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION NARY-UNHIDE-HIDE-WRAPPER))
 )
(NARY-*META*-UNHIDE-HIDE
 (58 29 (:REWRITE DEFAULT-+-2))
 (46 4 (:DEFINITION PAIRLIS$))
 (29 29 (:REWRITE DEFAULT-+-1))
 (26 2 (:REWRITE CAR-UNHIDE-EVAL-LIST))
 (24 6 (:DEFINITION SYMBOL-LISTP))
 (20 20 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 12 (:REWRITE UNHIDE-EVAL-CONSTRAINT-3))
 (15 12 (:REWRITE UNHIDE-EVAL-CONSTRAINT-2))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (14 2 (:DEFINITION ASSOC-EQUAL))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION PAIRLIS$))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-5))
 (2 2 (:REWRITE UNHIDE-EVAL-CONSTRAINT-4))
 (2 2 (:REWRITE CONSP-UNHIDE-EVAL-LIST))
 (2 2 (:REWRITE ASSOC-EQ-PAIRLIS$-NON-MEMBER))
 )
(FOO)
(OPEN-FOO
 (9 3 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:TYPE-PRESCRIPTION UNHIDE))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(FOO-0)
(FOO-10)
