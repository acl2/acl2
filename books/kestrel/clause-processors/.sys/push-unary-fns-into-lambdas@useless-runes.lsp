(PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (423 171 (:REWRITE DEFAULT-+-2))
 (247 171 (:REWRITE DEFAULT-+-1))
 (128 32 (:DEFINITION INTEGER-ABS))
 (53 38 (:REWRITE DEFAULT-<-2))
 (48 16 (:DEFINITION LENGTH))
 (42 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 7 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (6 3 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (2 2 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 )
(FREE-VARS-IN-TERM-OF-PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (99 19 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (75 23 (:DEFINITION QUOTEP))
 (69 9 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (48 6 (:DEFINITION QUOTE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION PUSH-UNARY-FN-INTO-LAMBDA-BODIES))
 (30 30 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (17 17 (:TYPE-PRESCRIPTION QUOTEP))
 (11 11 (:REWRITE FREE-VARS-IN-TERMS-WHEN-NOT-CONSP-CHEAP))
 )
(LOGIC-FNSP-OF-PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (77 77 (:TYPE-PRESCRIPTION PUSH-UNARY-FN-INTO-LAMBDA-BODIES))
 (26 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (21 21 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (20 10 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE TERMP-OF-CADR-WHEN-TERMP))
 (12 1 (:REWRITE NOT-MEMBER-EQUAL-OF-CDR-WHEN-NOT-MEMBER-EQUAL))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 1 (:DEFINITION ARGLISTP1))
 (9 9 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (8 8 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (8 8 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 1 (:DEFINITION LEGAL-VARIABLEP))
 (4 2 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (4 2 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (4 1 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (2 2 (:TYPE-PRESCRIPTION LEGAL-VARIABLE-OR-CONSTANT-NAMEP))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (2 2 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (2 2 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (2 2 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE MEMBER-EQUAL-OF-CAR-SAME))
 )
(TERMP-OF-PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (272 136 (:REWRITE DEFAULT-+-2))
 (226 14 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (184 24 (:REWRITE TERMP-OF-CADR-WHEN-TERMP))
 (156 13 (:REWRITE NOT-MEMBER-EQUAL-OF-CDR-WHEN-NOT-MEMBER-EQUAL))
 (136 136 (:REWRITE DEFAULT-+-1))
 (80 40 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (80 40 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (64 8 (:REWRITE DEFAULT-<-2))
 (60 60 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (60 15 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (57 57 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (57 57 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (53 53 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (40 40 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (40 40 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (40 40 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (40 40 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (40 40 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (40 10 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (32 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (30 15 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (20 10 (:DEFINITION QUOTEP))
 (15 15 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (13 13 (:REWRITE MEMBER-EQUAL-OF-CAR-SAME))
 (10 10 (:TYPE-PRESCRIPTION QUOTEP))
 (10 10 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:REWRITE DEFAULT-<-1))
 )
(LOGIC-TERMP-OF-PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (530 138 (:REWRITE LOGIC-TERMP-WHEN-QUOTEP))
 (312 24 (:REWRITE LOGIC-TERMP-OF-CAR-WHEN-LOGIC-TERM-LISTP))
 (296 99 (:DEFINITION QUOTEP))
 (228 114 (:REWRITE DEFAULT-+-2))
 (223 27 (:REWRITE LOGIC-TERM-LISTP-OF-CDR))
 (180 180 (:TYPE-PRESCRIPTION PUSH-UNARY-FN-INTO-LAMBDA-BODIES))
 (179 11 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (156 13 (:REWRITE NOT-MEMBER-EQUAL-OF-CDR-WHEN-NOT-MEMBER-EQUAL))
 (117 117 (:TYPE-PRESCRIPTION QUOTEP))
 (114 114 (:REWRITE DEFAULT-+-1))
 (108 12 (:REWRITE LOGIC-TERMP-OF-CADR-WHEN-LOGIC-TERMP))
 (74 37 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (74 37 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (60 15 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (44 44 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (43 43 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (43 43 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (43 43 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (37 37 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (37 37 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (37 37 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (37 37 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (37 37 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (32 16 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (28 7 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (16 16 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (14 14 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (13 13 (:REWRITE MEMBER-EQUAL-OF-CAR-SAME))
 (7 7 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 )
(PSEUDO-TERMP-OF-PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (287 263 (:REWRITE DEFAULT-CDR))
 (287 239 (:REWRITE DEFAULT-CAR))
 (114 57 (:REWRITE DEFAULT-+-2))
 (57 57 (:REWRITE DEFAULT-+-1))
 (37 37 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (30 12 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (20 20 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (15 15 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (13 13 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(PUSH-UNARY-FN-INTO-LAMBDA-BODIES-INDUCT
 (423 171 (:REWRITE DEFAULT-+-2))
 (247 171 (:REWRITE DEFAULT-+-1))
 (128 32 (:DEFINITION INTEGER-ABS))
 (53 38 (:REWRITE DEFAULT-<-2))
 (48 16 (:DEFINITION LENGTH))
 (42 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(IF-EVAL-OF-PUSH-UNARY-FN-INTO-LAMBDA-BODIES
 (113 105 (:REWRITE DEFAULT-CAR))
 (57 10 (:REWRITE IF-EVAL-LIST-WHEN-QUOTE-LISTP))
 (54 54 (:REWRITE DEFAULT-CDR))
 (51 20 (:REWRITE IF-EVAL-OF-QUOTE))
 (51 20 (:REWRITE IF-EVAL-OF-IF-CALL))
 (39 6 (:DEFINITION QUOTE-LISTP))
 (29 20 (:REWRITE IF-EVAL-OF-VARIABLE))
 (22 22 (:REWRITE NOT-IF-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-EVAL-AND-MEMBER-EQUAL))
 (14 14 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (12 4 (:REWRITE SYMBOL-LISTP-OF-CONS))
 (11 6 (:DEFINITION QUOTEP))
 (8 8 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (8 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (8 2 (:REWRITE SYMBOL-LISTP-OF-CDR))
 (7 7 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (4 4 (:REWRITE IF-EVAL-LIST-OF-ATOM))
 )
(PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM
 (95 95 (:REWRITE DEFAULT-CAR))
 (88 88 (:REWRITE DEFAULT-CDR))
 (46 23 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (24 24 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (12 12 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (12 6 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (12 6 (:DEFINITION TRUE-LISTP))
 (6 6 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (6 6 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (6 6 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (6 6 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (6 6 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 )
(LEN-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERMS
 (48 24 (:REWRITE DEFAULT-+-2))
 (38 37 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE DEFAULT-CAR))
 )
(FLAG-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM
 (194 93 (:REWRITE DEFAULT-+-2))
 (134 93 (:REWRITE DEFAULT-+-1))
 (88 22 (:REWRITE COMMUTATIVITY-OF-+))
 (88 22 (:DEFINITION INTEGER-ABS))
 (33 11 (:DEFINITION LENGTH))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (29 25 (:REWRITE DEFAULT-<-2))
 (28 25 (:REWRITE DEFAULT-<-1))
 (24 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 21 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-REALPART))
 (11 11 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-IMAGPART))
 (11 11 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM-EQUIVALENCES)
(FLAG-LEMMA-FOR-PSEUDO-TERMP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM
 (731 715 (:REWRITE DEFAULT-CDR))
 (710 677 (:REWRITE DEFAULT-CAR))
 (260 130 (:REWRITE DEFAULT-+-2))
 (180 180 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (163 163 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (150 73 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (130 130 (:REWRITE DEFAULT-+-1))
 (89 77 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (83 83 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (76 35 (:DEFINITION TRUE-LISTP))
 (44 44 (:TYPE-PRESCRIPTION PUSH-UNARY-FN-INTO-LAMBDA-BODIES))
 (41 41 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (37 37 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 (36 18 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (36 18 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (18 18 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (18 18 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (18 18 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (18 18 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (18 18 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM))
 )
(PSEUDO-TERMP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM)
(PSEUDO-TERM-LISTP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERMS)
(FLAG-LEMMA-FOR-LOGIC-TERMP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM
 (680 19 (:REWRITE TERMP-OF-CADR-WHEN-TERMP))
 (666 666 (:REWRITE DEFAULT-CDR))
 (646 640 (:REWRITE DEFAULT-CAR))
 (290 145 (:REWRITE DEFAULT-+-2))
 (230 19 (:REWRITE NOT-MEMBER-EQUAL-OF-CDR-WHEN-NOT-MEMBER-EQUAL))
 (145 145 (:REWRITE DEFAULT-+-1))
 (126 63 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (126 63 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (106 29 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (102 51 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (63 63 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (63 63 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (63 63 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (63 63 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (63 63 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (63 57 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (55 55 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (37 9 (:REWRITE LOGIC-TERMP-WHEN-QUOTEP))
 (35 35 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (35 35 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (33 33 (:REWRITE DEFAULT-COERCE-2))
 (33 33 (:REWRITE DEFAULT-COERCE-1))
 (32 32 (:TYPE-PRESCRIPTION PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM))
 (25 25 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (25 9 (:DEFINITION QUOTEP))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (21 19 (:REWRITE MEMBER-EQUAL-OF-CAR-SAME))
 (12 12 (:TYPE-PRESCRIPTION LOGIC-FNS-LISTP))
 (9 9 (:TYPE-PRESCRIPTION QUOTEP))
 (8 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (8 1 (:DEFINITION TERM-LISTP))
 (4 4 (:REWRITE ARITIES-OKP-WHEN-ARITIES-OKP-AND-SUBSETP-EQUAL))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (2 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 )
(LOGIC-TERMP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM)
(LOGIC-TERM-LISTP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERMS)
(IF-EVAL-LIST-WHEN-NOT-EMPTY
 (34 3 (:REWRITE IF-EVAL-LIST-WHEN-QUOTE-LISTP))
 (28 3 (:DEFINITION QUOTE-LISTP))
 (13 3 (:REWRITE IF-EVAL-LIST-WHEN-SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE DEFAULT-CDR))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 3 (:DEFINITION QUOTEP))
 (5 2 (:REWRITE IF-EVAL-OF-VARIABLE))
 (4 1 (:REWRITE SYMBOL-LISTP-OF-CDR))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 2 (:REWRITE IF-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE NOT-IF-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE IF-EVAL-OF-QUOTE))
 (2 2 (:REWRITE IF-EVAL-OF-IF-CALL))
 (2 2 (:REWRITE IF-EVAL-LIST-OF-ATOM))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LEN-HELPER
 (44 22 (:REWRITE DEFAULT-+-2))
 (27 27 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE DEFAULT-+-1))
 )
(FLAG-LEMMA-FOR-IF-EVAL-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM
 (780 39 (:REWRITE IF-EVAL-LIST-WHEN-QUOTE-LISTP))
 (672 41 (:DEFINITION QUOTE-LISTP))
 (573 247 (:REWRITE DEFAULT-CAR))
 (384 8 (:REWRITE CDR-OF-IF-EVAL-LIST))
 (280 147 (:REWRITE DEFAULT-CDR))
 (171 171 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (152 8 (:REWRITE CAR-OF-IF-EVAL-LIST))
 (150 36 (:REWRITE SYMBOL-LISTP-OF-CDR))
 (131 48 (:REWRITE IF-EVAL-OF-LAMBDA-BETTER))
 (123 46 (:REWRITE IF-EVAL-OF-VARIABLE))
 (113 48 (:REWRITE IF-EVAL-OF-IF-CALL))
 (89 36 (:DEFINITION QUOTEP))
 (78 78 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (78 39 (:REWRITE DEFAULT-<-2))
 (62 30 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (49 49 (:TYPE-PRESCRIPTION PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM))
 (48 48 (:REWRITE NOT-IF-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-EVAL-AND-MEMBER-EQUAL))
 (44 44 (:TYPE-PRESCRIPTION KWOTE-LST))
 (40 34 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (39 39 (:REWRITE DEFAULT-<-1))
 (23 3 (:REWRITE SYMBOL-LISTP-OF-CONS))
 (20 10 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (20 10 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (10 10 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (10 10 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (10 10 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 )
(IF-EVAL-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM)
(IF-EVAL-LIST-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERMS)
(PUSH-UNARY-FNS-INTO-LAMBDAS-IN-LITERALS
 (6 6 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM))
 )
(LOGIC-TERM-LISTP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-LITERALS
 (9 1 (:REWRITE LOGIC-TERM-LISTP-OF-CDR-WHEN-LOGIC-TERMP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE LOGIC-TERMP-WHEN-CONSP))
 (4 1 (:REWRITE LOGIC-TERMP-WHEN-QUOTEP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 )
(PSEUDO-TERM-LIST-LISTP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-LITERALS
 (186 3 (:DEFINITION PSEUDO-TERMP))
 (83 55 (:REWRITE DEFAULT-CAR))
 (65 17 (:REWRITE LEN-HELPER))
 (52 48 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (20 20 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (11 5 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (9 3 (:DEFINITION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (6 6 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION PUSH-UNARY-FNS-INTO-LAMBDAS-IN-TERM))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (3 3 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 )
(IF-EVAL-OF-DISJOIN-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-IN-LITERALS
 (283 5 (:DEFINITION PSEUDO-TERMP))
 (218 44 (:REWRITE LEN-HELPER))
 (152 107 (:REWRITE DEFAULT-CAR))
 (143 42 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-EVAL-WHEN-NOT-CONSP))
 (104 99 (:REWRITE DEFAULT-CDR))
 (45 45 (:TYPE-PRESCRIPTION PUSH-UNARY-FNS-INTO-LAMBDAS-IN-LITERALS))
 (45 45 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (45 45 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (42 42 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (42 21 (:REWRITE NOT-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CDR-CHEAP))
 (42 21 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP))
 (28 28 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (28 14 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (24 7 (:REWRITE IF-EVAL-OF-VARIABLE))
 (21 21 (:REWRITE MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL))
 (21 21 (:REWRITE MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF))
 (21 21 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR))
 (21 21 (:REWRITE MEMBER-EQUAL-OF-CONSTANT-TRIM))
 (17 17 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-AND-SYMBOL-LISTP))
 (16 9 (:REWRITE IF-EVAL-OF-LAMBDA-BETTER))
 (14 14 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (10 5 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE IF-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-EVAL-AND-MEMBER-EQUAL))
 (9 9 (:REWRITE IF-EVAL-OF-IF-CALL))
 (5 5 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (5 5 (:REWRITE LEN-OF-LAMBDA-FORMALS-OF-CAR-WHEN-TERMP))
 )
(PUSH-UNARY-FNS-INTO-LAMBDAS-CLAUSE-PROCESSOR)
(LOGIC-TERM-LIST-LISTP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-CLAUSE-PROCESSOR)
(PSEUDO-TERM-LIST-LISTP-OF-PUSH-UNARY-FNS-INTO-LAMBDAS-CLAUSE-PROCESSOR
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(PUSH-UNARY-FNS-INTO-LAMBDAS-CLAUSE-PROCESSOR-CORRECT
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE NOT-IF-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-EVAL-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(PUSH-UNARY-FNS-INTO-LAMBDAS-FOR-ALL-GOALS)
