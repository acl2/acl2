(APPLY-FOR-DEFEVALUATOR)
(MY-MAKE-FLAG-EVAL)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(MY-MAKE-FLAG-EVAL-OF-FNCALL-ARGS)
(MY-MAKE-FLAG-EVAL-OF-VARIABLE)
(MY-MAKE-FLAG-EVAL-OF-QUOTE)
(MY-MAKE-FLAG-EVAL-OF-LAMBDA)
(MY-MAKE-FLAG-EVAL-LIST-OF-ATOM)
(MY-MAKE-FLAG-EVAL-LIST-OF-CONS)
(MY-MAKE-FLAG-EVAL-OF-NONSYMBOL-ATOM)
(MY-MAKE-FLAG-EVAL-OF-BAD-FNCALL)
(MY-MAKE-FLAG-EVAL-OF-IF-CALL)
(MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL)
(MY-MAKE-FLAG-EVAL-OF-EQL-CALL)
(MY-MAKE-FLAG-EVAL-OF-EQ-CALL)
(MY-MAKE-FLAG-EVAL-OF-NOT-CALL)
(MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL)
(MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL)
(MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL)
(MY-MAKE-FLAG-EVAL-OF-MYIF-CALL)
(MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (19 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (10 10 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (8 8 (:REWRITE MY-MAKE-FLAG-EVAL-LIST-OF-CONS))
 (8 8 (:REWRITE MY-MAKE-FLAG-EVAL-LIST-OF-ATOM))
 )
(MY-MAKE-FLAG-EVAL-LIST-OF-APPEND
 (256 128 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (128 128 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (128 128 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (13 10 (:REWRITE DEFAULT-CAR))
 (12 9 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 )
(LEN-OF-MY-MAKE-FLAG-EVAL-LIST
 (14 7 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (1 1 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 )
(MY-MAKE-FLAG-EVAL-LIST-OF-TRUE-LIST_FIX
 (7 6 (:REWRITE DEFAULT-CAR))
 (6 5 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 )
(MY-MAKE-FLAG-EVAL-OF-FNCALL-ARGS-BACK)
(MY-MAKE-FLAG-EVAL-LIST-OF-DISJOIN2-IFF
 (49 49 (:REWRITE DEFAULT-CAR))
 (39 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (27 21 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (13 13 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 )
(MY-MAKE-FLAG-EVAL-LIST-OF-DISJOIN-OF-CONS-IFF
 (90 90 (:REWRITE DEFAULT-CAR))
 (53 53 (:REWRITE DEFAULT-CDR))
 (42 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (29 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (13 13 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 )
(ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL
 (3 1 (:DEFINITION ALISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP)
(ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-OF-CONS
 (10 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-OF-APPEND
 (90 45 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (64 64 (:REWRITE DEFAULT-CAR))
 (57 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (45 45 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (45 45 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (28 28 (:REWRITE DEFAULT-CDR))
 )
(MY-MAKE-FLAG-EVAL-OF-CONJOIN
 (150 150 (:REWRITE DEFAULT-CAR))
 (96 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (76 76 (:REWRITE DEFAULT-CDR))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (56 50 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (40 40 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 )
(MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL
 (17 17 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL
 (3 1 (:DEFINITION ALISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP)
(ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-OF-CONS
 (10 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-OF-APPEND
 (90 45 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (64 64 (:REWRITE DEFAULT-CAR))
 (57 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (45 45 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (45 45 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (30 30 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (28 28 (:REWRITE DEFAULT-CDR))
 )
(MY-MAKE-FLAG-EVAL-OF-DISJOIN
 (115 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (85 85 (:REWRITE DEFAULT-CAR))
 (61 61 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (58 58 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (57 57 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (23 23 (:REWRITE DEFAULT-CDR))
 )
(NOT-MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL
 (17 17 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-QUOTE))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL
 (44 18 (:REWRITE NOT-MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (38 38 (:REWRITE DEFAULT-CAR))
 (26 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (19 4 (:DEFINITION MEMBER-EQUAL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (16 16 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (14 14 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 )
(NOT-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T
 (52 9 (:REWRITE ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (37 37 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE DISJOIN-WHEN-NOT-CONSP))
 (12 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-LAMBDA-BETTER))
 (9 9 (:REWRITE ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-IF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (7 7 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-OF-VARIABLE))
 )
(ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-OF-SIMPLIFY-ASSUMPTIONS-IN-CLAUSE
 (65 65 (:REWRITE DEFAULT-CAR))
 (39 39 (:REWRITE DEFAULT-CDR))
 (24 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (24 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (24 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (24 23 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (23 22 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (23 22 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (23 22 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (19 10 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (9 9 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (8 8 (:REWRITE ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-LIST-OF-ATOM))
 (4 1 (:DEFINITION KWOTE-LST))
 (1 1 (:DEFINITION KWOTE))
 )
(RESOLVE-IFS-IN-CLAUSE-CORRECT-NEW)
(MY-MAKE-FLAG-EVAL-OF-DISJOIN-OF-FLATTEN-DISJUNCTS
 (89 89 (:REWRITE DEFAULT-CAR))
 (72 72 (:REWRITE DEFAULT-CDR))
 (44 44 (:REWRITE NOT-MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (38 37 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (38 37 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (38 37 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (19 19 (:TYPE-PRESCRIPTION MYIF))
 (18 18 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-LIST-OF-ATOM))
 (4 1 (:DEFINITION KWOTE-LST))
 (2 2 (:REWRITE MYIF-WHEN-NOT-NIL))
 (2 2 (:REWRITE MYIF-WHEN-NIL))
 (2 2 (:REWRITE MYIF-OF-CONSTANT-WHEN-NOT-NIL))
 (2 2 (:REWRITE BOOLOR-OF-NON-NIL-ARG2))
 (2 2 (:REWRITE BOOLOR-OF-NON-NIL))
 (2 2 (:REWRITE BOOLAND-OF-NON-NIL-ARG2))
 (2 2 (:REWRITE BOOLAND-OF-NON-NIL))
 (1 1 (:DEFINITION KWOTE))
 )
(MY-MAKE-FLAG-EVAL-OF-DISJOIN-OF-SUBLIS-VAR-AND-SIMPLIFY-LST
 (76 76 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE DEFAULT-CDR))
 (35 35 (:REWRITE NOT-MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (34 33 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (34 33 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (34 33 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (34 33 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-LIST-OF-ATOM))
 (4 4 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (4 1 (:DEFINITION KWOTE-LST))
 (1 1 (:DEFINITION KWOTE))
 )
(MY-MAKE-FLAG-EVAL-OF-DISJOIN-OF-PUSH-UNARY-FUNCTIONS-IN-LITERALS
 (51 51 (:REWRITE DEFAULT-CAR))
 (34 34 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE NOT-MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-NOT-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-MYIF-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQUAL-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQL-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-EQ-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLOR-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLIF-CALL))
 (16 15 (:REWRITE MY-MAKE-FLAG-EVAL-OF-BOOLAND-CALL))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (5 5 (:REWRITE MY-MAKE-FLAG-EVAL-LIST-OF-ATOM))
 (4 1 (:DEFINITION KWOTE-LST))
 (2 2 (:REWRITE MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (1 1 (:DEFINITION KWOTE))
 )
(MY-MAKE-FLAG-EVAL-OF-CONJOIN-OF-DISJOIN-LST-OF-CLAUSE-TO-CLAUSE-LIST)
(MY-MAKE-FLAG-EVAL-OF-DISJOIN-OF-HANDLE-CONSTANT-LITERALS)
(SIMPLIFY-AFTER-USING-CONJUNCTION-CLAUSE-PROCESSOR)
(SIMPLIFY-AFTER-USING-CONJUNCTION-CLAUSE-PROCESSOR-CORRECT
 (9 6 (:REWRITE DISJOIN-WHEN-NOT-CONSP))
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (4 2 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (4 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (3 3 (:TYPE-PRESCRIPTION SIMPLIFY-ASSUMPTIONS-IN-CLAUSE))
 (3 1 (:DEFINITION ALISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE NOT-MY-MAKE-FLAG-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-MY-MAKE-FLAG-EVAL-WHEN-NOT-CONSP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )