(APPLY-FOR-DEFEVALUATOR)
(CMR::FLATTEN-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(CMR::FLATTEN-EV-OF-FNCALL-ARGS)
(CMR::FLATTEN-EV-OF-VARIABLE)
(CMR::FLATTEN-EV-OF-QUOTE)
(CMR::FLATTEN-EV-OF-LAMBDA)
(CMR::FLATTEN-EV-LIST-OF-ATOM)
(CMR::FLATTEN-EV-LIST-OF-CONS)
(CMR::FLATTEN-EV-OF-NONSYMBOL-ATOM)
(CMR::FLATTEN-EV-OF-BAD-FNCALL)
(CMR::FLATTEN-EV-OF-NOT-CALL)
(CMR::FLATTEN-EV-OF-IF-CALL)
(CMR::FLATTEN-EV-OF-IMPLIES-CALL)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-FIX-X
 (46 40 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE DEFAULT-CDR))
 (16 10 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (16 10 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (16 10 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (16 10 (:REWRITE CMR::FLATTEN-EV-OF-BAD-FNCALL))
 (12 10 (:REWRITE CMR::FLATTEN-EV-OF-NONSYMBOL-ATOM))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (8 2 (:DEFINITION KWOTE-LST))
 (6 6 (:REWRITE CMR::FLATTEN-EV-LIST-OF-ATOM))
 (6 6 (:REWRITE CAR-CONS))
 (2 2 (:DEFINITION KWOTE))
 )
(CMR::FLATTEN-EV-PSEUDO-TERM-EQUIV-CONGRUENCE-ON-X)
(CMR::FLATTEN-EV-LIST-OF-PSEUDO-TERM-LIST-FIX-X)
(CMR::FLATTEN-EV-LIST-PSEUDO-TERM-LIST-EQUIV-CONGRUENCE-ON-X)
(CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-NULL)
(CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-QUOTE)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-QUOTE)
(CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-VAR)
(CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-FNCALL)
(CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-LAMBDA)
(CMR::FLATTEN-EV-OF-PSEUDO-TERM-CALL)
(CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-CALL)
(CMR::FLATTEN-EV-OF-PAIR-VARS)
(CMR::FLATTEN-EV-LIST-OF-PAIR-VARS)
(CMR::FLATTEN-EV-DISJOIN-CONS)
(CMR::FLATTEN-EV-DISJOIN-WHEN-CONSP)
(CMR::FLATTEN-EV-DISJOIN-ATOM
 (1 1 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 )
(CMR::FLATTEN-EV-DISJOIN-APPEND
 (23 23 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (23 23 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 )
(CMR::FLATTEN-EV-CONJOIN-CONS)
(CMR::FLATTEN-EV-CONJOIN-WHEN-CONSP)
(CMR::FLATTEN-EV-CONJOIN-ATOM
 (1 1 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 )
(CMR::FLATTEN-EV-CONJOIN-APPEND
 (23 23 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (23 23 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 )
(CMR::FLATTEN-EV-CONJOIN-CLAUSES-CONS
 (100 50 (:DEFINITION DISJOIN))
 (50 50 (:DEFINITION DISJOIN2))
 (7 7 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (5 5 (:REWRITE CMR::FLATTEN-EV-CONJOIN-ATOM))
 )
(CMR::FLATTEN-EV-CONJOIN-CLAUSES-WHEN-CONSP
 (24 24 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (24 24 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (18 9 (:DEFINITION DISJOIN))
 (9 9 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (9 9 (:DEFINITION DISJOIN2))
 )
(CMR::FLATTEN-EV-CONJOIN-CLAUSES-ATOM
 (1 1 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 )
(CMR::FLATTEN-EV-CONJOIN-CLAUSES-APPEND
 (65 65 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (65 65 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (24 12 (:DEFINITION DISJOIN))
 (12 12 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (12 12 (:DEFINITION DISJOIN2))
 )
(CMR::PSEUDO-TERM-LISTP-OF-APPEND
 (44 44 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (17 15 (:REWRITE DEFAULT-CAR))
 (16 14 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(CMR::DUMB-NEGATE
 (90 18 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (90 18 (:DEFINITION LEN))
 (90 6 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (84 84 (:REWRITE DEFAULT-CDR))
 (78 78 (:REWRITE DEFAULT-CAR))
 (36 18 (:REWRITE DEFAULT-+-2))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 6 (:DEFINITION TRUE-LISTP))
 )
(CMR::PSEUDO-TERMP-OF-DUMB-NEGATE
 (398 6 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (79 79 (:TYPE-PRESCRIPTION LEN))
 (75 72 (:REWRITE DEFAULT-CAR))
 (75 15 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (75 15 (:DEFINITION LEN))
 (75 5 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (74 74 (:REWRITE DEFAULT-CDR))
 (31 31 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (30 15 (:REWRITE DEFAULT-+-2))
 (27 5 (:DEFINITION SYMBOL-LISTP))
 (22 5 (:DEFINITION TRUE-LISTP))
 (21 21 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (15 15 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (5 5 (:TYPE-PRESCRIPTION PSEUDO-TERM-CALL->ARGS))
 )
(CMR::DUMB-NEGATE-CORRECT
 (594 6 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (570 6 (:DEFINITION PSEUDO-TERMP))
 (195 23 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (193 21 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (193 21 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-QUOTE))
 (193 21 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (126 105 (:REWRITE DEFAULT-CAR))
 (108 108 (:TYPE-PRESCRIPTION LEN))
 (92 90 (:REWRITE DEFAULT-CDR))
 (90 90 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (90 18 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (90 18 (:DEFINITION LEN))
 (90 6 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (59 17 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (59 17 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (36 36 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (36 18 (:REWRITE DEFAULT-+-2))
 (36 6 (:DEFINITION SYMBOL-LISTP))
 (35 11 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (35 11 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (35 11 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (30 6 (:DEFINITION TRUE-LISTP))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:REWRITE PSEUDO-TERM-KIND$INLINE-OF-PSEUDO-TERM-FIX-X))
 (18 18 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(CMR::DUMB-CONJUNCTION-TO-LITERALS
 (176 107 (:REWRITE DEFAULT-CDR))
 (118 88 (:REWRITE DEFAULT-CAR))
 (90 18 (:DEFINITION LEN))
 (36 18 (:REWRITE DEFAULT-+-2))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 6 (:DEFINITION TRUE-LISTP))
 (4 1 (:LINEAR PSEUDO-TERM-LIST-COUNT-OF-CDR))
 (4 1 (:LINEAR PSEUDO-TERM-COUNT-OF-CAR))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(CMR::PSEUDO-TERM-LISTP-OF-DUMB-CONJUNCTION-TO-LITERALS
 (396 4 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (380 4 (:DEFINITION PSEUDO-TERMP))
 (163 92 (:REWRITE DEFAULT-CDR))
 (127 80 (:REWRITE DEFAULT-CAR))
 (125 25 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (125 17 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (77 77 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (72 72 (:TYPE-PRESCRIPTION LEN))
 (60 12 (:DEFINITION LEN))
 (37 37 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (24 4 (:DEFINITION SYMBOL-LISTP))
 (21 21 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (20 4 (:DEFINITION TRUE-LISTP))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(CMR::DUMB-CONJUNCTION-TO-LITERALS-CORRECT
 (1881 19 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (1805 19 (:DEFINITION PSEUDO-TERMP))
 (433 309 (:REWRITE DEFAULT-CAR))
 (412 306 (:REWRITE DEFAULT-CDR))
 (404 58 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (387 47 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (372 42 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (342 342 (:TYPE-PRESCRIPTION LEN))
 (285 285 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (285 57 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (285 57 (:DEFINITION LEN))
 (285 19 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (149 40 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (131 37 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (114 114 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (114 57 (:REWRITE DEFAULT-+-2))
 (114 19 (:DEFINITION SYMBOL-LISTP))
 (95 95 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (95 95 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (95 19 (:DEFINITION TRUE-LISTP))
 (83 37 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (79 37 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (76 76 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (75 37 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (57 57 (:REWRITE DEFAULT-+-1))
 (38 38 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (23 13 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (10 10 (:TYPE-PRESCRIPTION CMR::DUMB-CONJUNCTION-TO-LITERALS))
 (2 2 (:REWRITE NOT-QUOTE-OF-PSEUDO-TERM-FNCALL->FN))
 )
(CMR::DUMB-FORMULA-TO-CLAUSE
 (92 86 (:REWRITE DEFAULT-CDR))
 (90 18 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (90 18 (:DEFINITION LEN))
 (86 80 (:REWRITE DEFAULT-CAR))
 (36 18 (:REWRITE DEFAULT-+-2))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 6 (:DEFINITION TRUE-LISTP))
 )
(CMR::PSEUDO-TERM-LISTP-OF-DUMB-FORMULA-TO-CLAUSE
 (396 4 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (380 4 (:DEFINITION PSEUDO-TERMP))
 (82 62 (:REWRITE DEFAULT-CAR))
 (78 64 (:REWRITE DEFAULT-CDR))
 (72 72 (:TYPE-PRESCRIPTION LEN))
 (60 12 (:DEFINITION LEN))
 (27 27 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (25 25 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (24 4 (:DEFINITION SYMBOL-LISTP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (20 4 (:DEFINITION TRUE-LISTP))
 (18 18 (:TYPE-PRESCRIPTION PSEUDO-TERM-CALL->ARGS))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 2 (:DEFINITION BINARY-APPEND))
 (9 9 (:TYPE-PRESCRIPTION CMR::DUMB-CONJUNCTION-TO-LITERALS))
 (9 9 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(CMR::DUMB-FORMULA-TO-CLAUSE-CORRECT
 (594 6 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (570 6 (:DEFINITION PSEUDO-TERMP))
 (244 32 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (241 29 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (229 25 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (134 95 (:REWRITE DEFAULT-CAR))
 (120 97 (:REWRITE DEFAULT-CDR))
 (108 108 (:TYPE-PRESCRIPTION LEN))
 (90 90 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (90 18 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (90 18 (:DEFINITION LEN))
 (90 6 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (51 18 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (51 18 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (51 18 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (51 18 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (51 18 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (36 36 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (36 18 (:REWRITE DEFAULT-+-2))
 (36 6 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (30 6 (:DEFINITION TRUE-LISTP))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:REWRITE PSEUDO-TERM-KIND$INLINE-OF-PSEUDO-TERM-FIX-X))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 3 (:DEFINITION BINARY-APPEND))
 (13 7 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 10 (:TYPE-PRESCRIPTION CMR::DUMB-CONJUNCTION-TO-LITERALS))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(CMR::DUMB-NEGATE-EACH
 (71 1 (:DEFINITION PSEUDO-TERMP))
 (40 8 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (35 4 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (17 17 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (15 3 (:DEFINITION LEN))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(CMR::PSEUDO-TERM-LISTP-OF-DUMB-NEGATE-EACH
 (35 7 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (35 7 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (30 30 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (10 9 (:REWRITE DEFAULT-CDR))
 (10 9 (:REWRITE DEFAULT-CAR))
 (7 7 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(CMR::DISJOIN-OF-DUMB-NEGATE-EACH
 (453 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (453 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (453 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (450 50 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (34 17 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (26 26 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE DEFAULT-CAR))
 (17 17 (:TYPE-PRESCRIPTION CMR::DUMB-NEGATE-EACH))
 )
(CMR::CONJOIN-OF-DUMB-NEGATE-EACH
 (507 57 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (507 57 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (507 57 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (504 56 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (38 19 (:REWRITE CMR::FLATTEN-EV-CONJOIN-ATOM))
 (28 28 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (19 19 (:TYPE-PRESCRIPTION CMR::DUMB-NEGATE-EACH))
 )
(CMR::FLATTEN-EV-OF-DISJOIN-PSEUDO-TERM-LIST-FIX
 (3753 31 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (2945 31 (:DEFINITION PSEUDO-TERMP))
 (1864 127 (:DEFINITION PSEUDO-TERM-LISTP))
 (1696 55 (:REWRITE PSEUDO-TERM-LIST-FIX-WHEN-PSEUDO-TERM-LISTP))
 (1464 273 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (1321 1321 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1302 184 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (606 606 (:REWRITE DEFAULT-CDR))
 (601 67 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (601 67 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (601 67 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (598 66 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (564 564 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (556 556 (:REWRITE DEFAULT-CAR))
 (465 93 (:DEFINITION LEN))
 (408 408 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (188 188 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (186 93 (:REWRITE DEFAULT-+-2))
 (186 31 (:DEFINITION SYMBOL-LISTP))
 (155 155 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (155 31 (:DEFINITION TRUE-LISTP))
 (124 124 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (93 93 (:REWRITE DEFAULT-+-1))
 (62 62 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (62 62 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (62 62 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (62 62 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (62 62 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (62 62 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (31 31 (:TYPE-PRESCRIPTION PSEUDO-TERM-LIST-FIX$INLINE))
 (20 20 (:REWRITE PSEUDO-TERM-KIND$INLINE-OF-PSEUDO-TERM-FIX-X))
 )
(CMR::DUMB-DISJOIN-LIT-LISTS)
(CMR::PSEUDO-TERM-LISTP-OF-DUMB-DISJOIN-LIT-LISTS)
(CMR::DUMB-DISJOIN-LIT-LISTS-CORRECT
 (1296 8 (:DEFINITION BINARY-APPEND))
 (980 44 (:REWRITE PSEUDO-TERM-LIST-FIX-WHEN-PSEUDO-TERM-LISTP))
 (960 8 (:REWRITE CAR-OF-PSEUDO-TERM-LIST-FIX))
 (944 8 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (892 60 (:DEFINITION PSEUDO-TERM-LISTP))
 (760 8 (:DEFINITION PSEUDO-TERMP))
 (532 532 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (447 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (447 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (447 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (441 49 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (368 92 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (368 76 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (312 8 (:REWRITE CDR-OF-PSEUDO-TERM-LIST-FIX))
 (228 228 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (180 180 (:REWRITE DEFAULT-CDR))
 (172 172 (:REWRITE DEFAULT-CAR))
 (160 160 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (144 144 (:TYPE-PRESCRIPTION LEN))
 (120 24 (:DEFINITION LEN))
 (91 49 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (76 76 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (49 49 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (49 49 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (49 49 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (49 49 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (49 49 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (49 49 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (48 24 (:REWRITE DEFAULT-+-2))
 (48 8 (:DEFINITION SYMBOL-LISTP))
 (40 40 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (40 8 (:DEFINITION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 24 (:REWRITE DEFAULT-+-1))
 (12 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (8 8 (:REWRITE CONSP-OF-PSEUDO-TERM-LIST-FIX))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (2 2 (:REWRITE-QUOTED-CONSTANT PSEUDO-TERM-FIX-UNDER-PSEUDO-TERM-EQUIV))
 )
(CMR::FLATTEN-EV-OF-CONJOIN-PSEUDO-TERM-LIST-FIX
 (2866 23 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (2185 23 (:DEFINITION PSEUDO-TERMP))
 (1569 107 (:DEFINITION PSEUDO-TERM-LISTP))
 (1416 45 (:REWRITE PSEUDO-TERM-LIST-FIX-WHEN-PSEUDO-TERM-LISTP))
 (1224 224 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (1066 1066 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1062 151 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (469 469 (:REWRITE DEFAULT-CDR))
 (463 52 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (463 52 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (463 52 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (460 51 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (456 456 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (427 427 (:REWRITE DEFAULT-CAR))
 (345 69 (:DEFINITION LEN))
 (328 328 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (152 152 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (138 69 (:REWRITE DEFAULT-+-2))
 (138 23 (:DEFINITION SYMBOL-LISTP))
 (115 115 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (115 23 (:DEFINITION TRUE-LISTP))
 (92 92 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (69 69 (:REWRITE DEFAULT-+-1))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (50 50 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (23 23 (:TYPE-PRESCRIPTION PSEUDO-TERM-LIST-FIX$INLINE))
 (5 5 (:REWRITE PSEUDO-TERM-KIND$INLINE-OF-PSEUDO-TERM-FIX-X))
 )
(CMR::DUMB-CONJOIN-LIT-LISTS)
(CMR::PSEUDO-TERM-LISTP-OF-DUMB-CONJOIN-LIT-LISTS)
(CMR::DUMB-CONJOIN-LIT-LISTS-CORRECT
 (810 5 (:DEFINITION BINARY-APPEND))
 (600 5 (:REWRITE CAR-OF-PSEUDO-TERM-LIST-FIX))
 (590 5 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (527 23 (:REWRITE PSEUDO-TERM-LIST-FIX-WHEN-PSEUDO-TERM-LISTP))
 (490 33 (:DEFINITION PSEUDO-TERM-LISTP))
 (475 5 (:DEFINITION PSEUDO-TERMP))
 (303 35 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (303 35 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (303 35 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (301 301 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (297 33 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (221 53 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (221 43 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (195 5 (:REWRITE CDR-OF-PSEUDO-TERM-LIST-FIX))
 (129 129 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (108 108 (:REWRITE DEFAULT-CDR))
 (103 103 (:REWRITE DEFAULT-CAR))
 (91 91 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (90 90 (:TYPE-PRESCRIPTION LEN))
 (75 15 (:DEFINITION LEN))
 (65 33 (:REWRITE CMR::FLATTEN-EV-CONJOIN-ATOM))
 (43 43 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (33 33 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (33 33 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (33 33 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (33 33 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (33 33 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (33 33 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (30 15 (:REWRITE DEFAULT-+-2))
 (30 5 (:DEFINITION SYMBOL-LISTP))
 (25 25 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (25 5 (:DEFINITION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (15 15 (:REWRITE DEFAULT-+-1))
 (12 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (5 5 (:REWRITE CONSP-OF-PSEUDO-TERM-LIST-FIX))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (2 2 (:REWRITE-QUOTED-CONSTANT PSEUDO-TERM-FIX-UNDER-PSEUDO-TERM-EQUIV))
 )
(CMR::DUMB-FLATTEN-DISJUNCTION
 (106 106 (:REWRITE DEFAULT-CDR))
 (92 46 (:REWRITE DEFAULT-+-2))
 (56 44 (:REWRITE DEFAULT-CAR))
 (46 46 (:REWRITE DEFAULT-+-1))
 (36 8 (:REWRITE AND*-REM-SECOND))
 (24 12 (:REWRITE DEFAULT-<-2))
 (24 12 (:REWRITE DEFAULT-<-1))
 (24 8 (:REWRITE AND*-REM-FIRST))
 )
(CMR::DUMB-FLATTEN-DISJUNCTION-FLAG
 (234 117 (:REWRITE DEFAULT-+-2))
 (199 199 (:REWRITE DEFAULT-CDR))
 (117 117 (:REWRITE DEFAULT-+-1))
 (75 57 (:REWRITE DEFAULT-CAR))
 (64 14 (:REWRITE AND*-REM-SECOND))
 (42 14 (:REWRITE AND*-REM-FIRST))
 (28 14 (:REWRITE DEFAULT-<-2))
 (28 14 (:REWRITE DEFAULT-<-1))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(CMR::DUMB-FLATTEN-DISJUNCTION-FLAG-EQUIVALENCES)
(CMR::FLAG-LEMMA-FOR-RETURN-TYPE-OF-DUMB-FLATTEN-DISJUNCTION.LITS
 (1059 1059 (:REWRITE DEFAULT-CDR))
 (932 466 (:REWRITE DEFAULT-+-2))
 (860 172 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (860 156 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (792 8 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (760 8 (:DEFINITION PSEUDO-TERMP))
 (640 640 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (541 511 (:REWRITE DEFAULT-CAR))
 (466 466 (:REWRITE DEFAULT-+-1))
 (297 91 (:REWRITE AND*-REM-SECOND))
 (273 91 (:REWRITE AND*-REM-FIRST))
 (196 196 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (164 164 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (48 8 (:DEFINITION SYMBOL-LISTP))
 (40 40 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (40 8 (:DEFINITION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(CMR::RETURN-TYPE-OF-DUMB-FLATTEN-DISJUNCTION.LITS)
(CMR::RETURN-TYPE-OF-DUMB-FLATTEN-CONJUNCTION.LITS)
(CMR::DUMB-FLATTEN-DISJUNCTION
 (1211 191 (:DEFINITION LEN))
 (1006 568 (:REWRITE DEFAULT-CDR))
 (653 368 (:REWRITE DEFAULT-CAR))
 (382 191 (:REWRITE DEFAULT-+-2))
 (240 108 (:REWRITE AND*-REM-SECOND))
 (191 191 (:REWRITE DEFAULT-+-1))
 (105 105 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (63 21 (:DEFINITION SYMBOL-LISTP))
 (42 42 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (42 21 (:DEFINITION TRUE-LISTP))
 )
(CMR::FLAG-LEMMA-FOR-DUMB-FLATTEN-DISJUNCTION-CORRECT
 (15795 5945 (:REWRITE DEFAULT-CAR))
 (14191 6402 (:REWRITE DEFAULT-CDR))
 (11367 965 (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (5415 57 (:DEFINITION PSEUDO-TERMP))
 (4763 965 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (4213 563 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (4117 491 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (3728 1864 (:REWRITE DEFAULT-+-2))
 (2411 763 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (2400 792 (:REWRITE AND*-REM-SECOND))
 (2376 792 (:REWRITE AND*-REM-FIRST))
 (2355 2355 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1864 1864 (:REWRITE DEFAULT-+-1))
 (1250 1250 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (908 908 (:REWRITE PSEUDO-TERM-LISTP-OF-PSEUDO-TERM-CALL->ARGS))
 (730 410 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (614 410 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (440 410 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (342 57 (:DEFINITION SYMBOL-LISTP))
 (313 121 (:REWRITE CMR::FLATTEN-EV-DISJOIN-ATOM))
 (285 285 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (285 285 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (285 57 (:DEFINITION TRUE-LISTP))
 (228 228 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (144 66 (:REWRITE CMR::FLATTEN-EV-CONJOIN-ATOM))
 (114 114 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (97 97 (:TYPE-PRESCRIPTION CMR::DUMB-FLATTEN-DISJUNCTION))
 (58 58 (:REWRITE NOT-QUOTE-OF-PSEUDO-TERM-FNCALL->FN))
 (54 54 (:TYPE-PRESCRIPTION CMR::DUMB-FLATTEN-CONJUNCTION))
 (26 26 (:TYPE-PRESCRIPTION CMR::DUMB-DISJOIN-LIT-LISTS))
 (9 9 (:TYPE-PRESCRIPTION CMR::DUMB-NEGATE-EACH))
 (7 7 (:REWRITE-QUOTED-CONSTANT PSEUDO-TERM-FIX-UNDER-PSEUDO-TERM-EQUIV))
 (6 6 (:TYPE-PRESCRIPTION CMR::DUMB-CONJOIN-LIT-LISTS))
 )
(CMR::DUMB-FLATTEN-DISJUNCTION-CORRECT)
(CMR::DUMB-FLATTEN-CONJUNCTION-CORRECT)
(CMR::FLAG-LEMMA-FOR-DUMB-FLATTEN-DISJUNCTION-OF-PSEUDO-TERM-FIX-X
 (10070 106 (:DEFINITION PSEUDO-TERMP))
 (2461 2461 (:REWRITE DEFAULT-CDR))
 (1844 922 (:REWRITE DEFAULT-+-2))
 (1652 1640 (:REWRITE DEFAULT-CAR))
 (922 922 (:REWRITE DEFAULT-+-1))
 (636 106 (:DEFINITION SYMBOL-LISTP))
 (530 530 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (530 530 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (530 106 (:DEFINITION TRUE-LISTP))
 (424 424 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (302 96 (:REWRITE AND*-REM-SECOND))
 (278 96 (:REWRITE AND*-REM-FIRST))
 (212 212 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(CMR::DUMB-FLATTEN-DISJUNCTION-OF-PSEUDO-TERM-FIX-X)
(CMR::DUMB-FLATTEN-CONJUNCTION-OF-PSEUDO-TERM-FIX-X)
(CMR::DUMB-FLATTEN-DISJUNCTION-PSEUDO-TERM-EQUIV-CONGRUENCE-ON-X)
(CMR::DUMB-FLATTEN-CONJUNCTION-PSEUDO-TERM-EQUIV-CONGRUENCE-ON-X)
(CMR::DUMB-FLATTEN-CLAUSE
 (655 9 (:DEFINITION PSEUDO-TERMP))
 (161 161 (:REWRITE DEFAULT-CDR))
 (150 150 (:REWRITE DEFAULT-CAR))
 (135 27 (:DEFINITION LEN))
 (114 114 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (85 85 (:TYPE-PRESCRIPTION LEN))
 (54 27 (:REWRITE DEFAULT-+-2))
 (41 41 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (33 9 (:DEFINITION SYMBOL-LISTP))
 (27 27 (:REWRITE DEFAULT-+-1))
 (24 9 (:DEFINITION TRUE-LISTP))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(CMR::PSEUDO-TERM-LISTP-OF-DUMB-FLATTEN-CLAUSE
 (126 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (35 7 (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
 (35 7 (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
 (28 28 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (7 7 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(CMR::DUMB-FLATTEN-CLAUSE-CORRECT
 (507 57 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-VAR))
 (507 57 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (507 57 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-FNCALL))
 (504 56 (:REWRITE CMR::FLATTEN-EV-WHEN-PSEUDO-TERM-NULL))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-VARIABLE))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-QUOTE))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-NOT-CALL))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-LAMBDA))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-IMPLIES-CALL))
 (56 56 (:REWRITE CMR::FLATTEN-EV-OF-IF-CALL))
 (28 28 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (17 17 (:TYPE-PRESCRIPTION CMR::DUMB-FLATTEN-CLAUSE))
 )
(CMR::DUMB-FLATTEN-CLAUSE-PROC)
(CMR::DUMB-FLATTEN-CLAUSE-PROC-CORRECT)
