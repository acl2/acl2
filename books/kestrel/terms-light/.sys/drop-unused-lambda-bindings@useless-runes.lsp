(DROP-UNUSED-LAMBDA-BINDINGS
 (455 187 (:REWRITE DEFAULT-+-2))
 (263 187 (:REWRITE DEFAULT-+-1))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (80 16 (:DEFINITION LEN))
 (53 38 (:REWRITE DEFAULT-<-2))
 (42 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (1 1 (:TYPE-PRESCRIPTION DROP-UNUSED-LAMBDA-BINDINGS))
 )
(FLAG-DROP-UNUSED-LAMBDA-BINDINGS
 (671 291 (:REWRITE DEFAULT-+-2))
 (408 291 (:REWRITE DEFAULT-+-1))
 (216 54 (:DEFINITION INTEGER-ABS))
 (216 27 (:DEFINITION LENGTH))
 (135 27 (:DEFINITION LEN))
 (82 63 (:REWRITE DEFAULT-<-2))
 (70 63 (:REWRITE DEFAULT-<-1))
 (54 54 (:REWRITE DEFAULT-UNARY-MINUS))
 (27 27 (:TYPE-PRESCRIPTION LEN))
 (27 27 (:REWRITE DEFAULT-REALPART))
 (27 27 (:REWRITE DEFAULT-NUMERATOR))
 (27 27 (:REWRITE DEFAULT-IMAGPART))
 (27 27 (:REWRITE DEFAULT-DENOMINATOR))
 (27 27 (:REWRITE DEFAULT-COERCE-2))
 (27 27 (:REWRITE DEFAULT-COERCE-1))
 (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-DROP-UNUSED-LAMBDA-BINDINGS-EQUIVALENCES)
(FLAG-LEMMA-FOR-PSEUDO-TERMP-OF-DROP-UNUSED-LAMBDA-BINDINGS
 (336 39 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP))
 (324 323 (:REWRITE DEFAULT-CDR))
 (313 311 (:REWRITE DEFAULT-CAR))
 (202 202 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (154 14 (:DEFINITION INTERSECTION-EQUAL))
 (148 35 (:REWRITE SYMBOL-LISTP-OF-CDR))
 (105 14 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (90 45 (:REWRITE DEFAULT-+-2))
 (87 87 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (84 39 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (78 13 (:DEFINITION QUOTEP))
 (70 14 (:DEFINITION MEMBER-EQUAL))
 (45 45 (:REWRITE DEFAULT-+-1))
 (40 40 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (35 35 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (30 15 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (28 28 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (28 14 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (14 14 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (13 13 (:TYPE-PRESCRIPTION QUOTEP))
 (8 1 (:REWRITE SYMBOL-LISTP-OF-CONS))
 )
(PSEUDO-TERMP-OF-DROP-UNUSED-LAMBDA-BINDINGS)
(PSEUDO-TERM-LISTP-OF-DROP-UNUSED-LAMBDA-BINDINGS-LST)
(LEN-OF-DROP-UNUSED-LAMBDA-BINDINGS-LST
 (40 20 (:REWRITE DEFAULT-+-2))
 (39 38 (:REWRITE DEFAULT-CDR))
 (30 1 (:DEFINITION DROP-UNUSED-LAMBDA-BINDINGS))
 (20 20 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE DEFAULT-CAR))
 (12 1 (:REWRITE MV-NTH-0-OF-FILTER-FORMALS-AND-ACTUALS))
 (11 1 (:DEFINITION INTERSECTION-EQUAL))
 (8 1 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (6 1 (:DEFINITION QUOTEP))
 (5 5 (:TYPE-PRESCRIPTION DROP-UNUSED-LAMBDA-BINDINGS))
 (5 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (2 1 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(DROP-UNUSED-LAMBDA-BINDINGS
 (81 81 (:REWRITE DEFAULT-CDR))
 (65 65 (:REWRITE DEFAULT-CAR))
 (32 32 (:TYPE-PRESCRIPTION DROP-UNUSED-LAMBDA-BINDINGS))
 (30 1 (:DEFINITION DROP-UNUSED-LAMBDA-BINDINGS))
 (28 14 (:REWRITE DEFAULT-+-2))
 (18 9 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (16 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (14 14 (:REWRITE DEFAULT-+-1))
 (12 6 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (12 2 (:DEFINITION QUOTEP))
 (12 1 (:REWRITE MV-NTH-0-OF-FILTER-FORMALS-AND-ACTUALS))
 (11 1 (:DEFINITION INTERSECTION-EQUAL))
 (8 4 (:DEFINITION TRUE-LISTP))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 7 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (6 2 (:DEFINITION DROP-UNUSED-LAMBDA-BINDINGS-LST))
 (5 1 (:DEFINITION MEMBER-EQUAL))
 (4 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
