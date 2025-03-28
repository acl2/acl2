(NO-NILS-IN-TERMP
 (530 224 (:REWRITE DEFAULT-+-2))
 (316 224 (:REWRITE DEFAULT-+-1))
 (152 38 (:DEFINITION INTEGER-ABS))
 (152 19 (:DEFINITION LENGTH))
 (62 44 (:REWRITE DEFAULT-<-2))
 (48 44 (:REWRITE DEFAULT-<-1))
 (38 38 (:REWRITE DEFAULT-UNARY-MINUS))
 (19 19 (:REWRITE DEFAULT-REALPART))
 (19 19 (:REWRITE DEFAULT-NUMERATOR))
 (19 19 (:REWRITE DEFAULT-IMAGPART))
 (19 19 (:REWRITE DEFAULT-DENOMINATOR))
 (19 19 (:REWRITE DEFAULT-COERCE-2))
 (19 19 (:REWRITE DEFAULT-COERCE-1))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 3 (:DEFINITION NO-NILS-IN-TERMSP))
 (11 11 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 3 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(NO-NILS-IN-TERMSP-OF-CDR
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(NO-NILS-IN-TERMP-OF-CONS
 (16 4 (:REWRITE NO-NILS-IN-TERMSP-OF-CDR))
 (16 2 (:DEFINITION NO-NILS-IN-TERMSP))
 (15 15 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(FLAG-LEMMA-FOR-NOT-MEMBER-EQUAL-OF-NIL-AND-FREE-VARS-IN-TERM
 (143 12 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (108 13 (:DEFINITION QUOTE-LISTP))
 (77 77 (:REWRITE DEFAULT-CAR))
 (62 62 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (56 56 (:REWRITE DEFAULT-CDR))
 (14 7 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (14 7 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 )
(NOT-MEMBER-EQUAL-OF-NIL-AND-FREE-VARS-IN-TERM)
(NOT-MEMBER-EQUAL-OF-NIL-AND-FREE-VARS-IN-TERMS)
(NO-NILS-IN-TERMP-WHEN-SYMBOLP)
(NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP
 (96 17 (:REWRITE NO-NILS-IN-TERMSP-OF-CDR))
 (41 41 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE DEFAULT-CDR))
 (20 20 (:TYPE-PRESCRIPTION NO-NILS-IN-TERMP))
 (15 1 (:DEFINITION NO-NILS-IN-TERMP))
 )
(NOT-MEMBER-EQUAL-OF-NIL-WHEN-NO-NILS-IN-TERMSP
 (184 18 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (135 22 (:DEFINITION SYMBOL-LISTP))
 (112 7 (:REWRITE NO-NILS-IN-TERMSP-OF-CDR))
 (94 94 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (38 38 (:REWRITE DEFAULT-CAR))
 (35 35 (:REWRITE DEFAULT-CDR))
 (30 1 (:DEFINITION NO-NILS-IN-TERMP))
 (6 6 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 )
(NO-NILS-IN-TERMP-OF-CAR
 (109 12 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (75 13 (:DEFINITION SYMBOL-LISTP))
 (60 2 (:DEFINITION NO-NILS-IN-TERMP))
 (58 58 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (52 4 (:REWRITE NO-NILS-IN-TERMSP-OF-CDR))
 (20 20 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 (1 1 (:REWRITE CDR-CONS))
 )
(NO-NILS-IN-TERMSP-OF-CONS
 (187 20 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (138 2 (:DEFINITION NO-NILS-IN-TERMP))
 (128 21 (:DEFINITION SYMBOL-LISTP))
 (104 8 (:REWRITE NO-NILS-IN-TERMSP-OF-CDR))
 (104 4 (:REWRITE NO-NILS-IN-TERMP-OF-CAR))
 (102 102 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (30 30 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 )
(NO-NILS-IN-TERMSP-OF-REMOVE-EQUAL
 (636 65 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (461 72 (:DEFINITION SYMBOL-LISTP))
 (323 323 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (138 2 (:DEFINITION NO-NILS-IN-TERMP))
 (116 116 (:REWRITE DEFAULT-CAR))
 (114 114 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 )
(NO-NILS-IN-TERMSP-OF-TAKE
 (916 98 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (641 101 (:DEFINITION SYMBOL-LISTP))
 (477 477 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (42 29 (:REWRITE DEFAULT-<-1))
 (36 23 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 (23 23 (:REWRITE DEFAULT-+-1))
 (11 8 (:REWRITE ZP-OPEN))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NO-NILS-IN-TERMSP-OF-UNION-EQUAL
 (4686 357 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (3670 377 (:DEFINITION SYMBOL-LISTP))
 (1784 1784 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1191 21 (:DEFINITION NO-NILS-IN-TERMP))
 (1178 589 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-UNION-EQUAL-TYPE))
 (1035 608 (:REWRITE DEFAULT-CDR))
 (913 612 (:REWRITE DEFAULT-CAR))
 (589 589 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (589 589 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (320 122 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 (41 41 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 )
(NO-NILS-IN-TERMSP-OF-INTERSECTION-EQUAL
 (4735 500 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (3314 529 (:DEFINITION SYMBOL-LISTP))
 (2502 2502 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2097 36 (:DEFINITION NO-NILS-IN-TERMP))
 (875 875 (:REWRITE DEFAULT-CAR))
 (873 873 (:REWRITE DEFAULT-CDR))
 (170 170 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 )
(NO-NILS-IN-TERMSP-OF-SET-DIFFERENCE-EQUAL
 (636 65 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (461 72 (:DEFINITION SYMBOL-LISTP))
 (323 323 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (138 2 (:DEFINITION NO-NILS-IN-TERMP))
 (116 116 (:REWRITE DEFAULT-CAR))
 (113 113 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 )
(NO-NILS-IN-TERMSP-OF-APPEND
 (1401 149 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (977 150 (:DEFINITION SYMBOL-LISTP))
 (722 722 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (215 215 (:REWRITE DEFAULT-CDR))
 (211 211 (:REWRITE DEFAULT-CAR))
 (207 3 (:DEFINITION NO-NILS-IN-TERMP))
 (96 48 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 48 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (42 42 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 )
(FLAG-NO-NILS-IN-TERMP
 (719 315 (:REWRITE DEFAULT-+-2))
 (447 315 (:REWRITE DEFAULT-+-1))
 (240 60 (:DEFINITION INTEGER-ABS))
 (240 30 (:DEFINITION LENGTH))
 (150 30 (:DEFINITION LEN))
 (92 69 (:REWRITE DEFAULT-<-2))
 (76 69 (:REWRITE DEFAULT-<-1))
 (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-NO-NILS-IN-TERMP-EQUIVALENCES)
(FLAG-LEMMA-FOR-NO-NILS-IN-TERMP-WHEN-TERMP
 (962 91 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (717 106 (:DEFINITION SYMBOL-LISTP))
 (500 500 (:REWRITE DEFAULT-CDR))
 (464 464 (:REWRITE DEFAULT-CAR))
 (461 461 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (122 61 (:REWRITE DEFAULT-+-2))
 (72 9 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (72 8 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (63 9 (:DEFINITION ARGLISTP1))
 (61 61 (:REWRITE DEFAULT-+-1))
 (59 25 (:DEFINITION MEMBER-EQUAL))
 (43 43 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 (40 8 (:DEFINITION ALL-VARS1))
 (21 21 (:REWRITE DEFAULT-COERCE-2))
 (21 21 (:REWRITE DEFAULT-COERCE-1))
 (17 17 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (16 8 (:DEFINITION ADD-TO-SET-EQUAL))
 (15 15 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (9 9 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 )
(NO-NILS-IN-TERMP-WHEN-TERMP)
(NO-NILS-IN-TERMSP-WHEN-TERM-LISTP)
(NO-NILS-IN-TERMP-WHEN-LOGIC-TERMP
 (132 1 (:DEFINITION TERMP))
 (45 4 (:DEFINITION LENGTH))
 (35 7 (:DEFINITION LEN))
 (34 34 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE DEFAULT-CAR))
 (17 1 (:DEFINITION ARGLISTP))
 (15 15 (:TYPE-PRESCRIPTION LEN))
 (14 7 (:REWRITE DEFAULT-+-2))
 (13 1 (:DEFINITION LOGIC-FNSP))
 (9 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (8 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (7 7 (:REWRITE DEFAULT-+-1))
 (7 3 (:DEFINITION MEMBER-EQUAL))
 (7 1 (:DEFINITION ARGLISTP1))
 (6 2 (:DEFINITION LEGAL-VARIABLEP))
 (6 1 (:DEFINITION ALL-VARS))
 (5 1 (:DEFINITION ALL-VARS1))
 (3 3 (:TYPE-PRESCRIPTION LEGAL-VARIABLE-OR-CONSTANT-NAMEP))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:TYPE-PRESCRIPTION TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ARGLISTP1))
 (2 2 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ADD-TO-SET-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION LOGICP))
 (1 1 (:TYPE-PRESCRIPTION ARITY))
 (1 1 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (1 1 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 )
(NO-NILS-IN-TERMSP-WHEN-LOGIC-TERM-LISTP
 (4 1 (:DEFINITION TERM-LISTP))
 (4 1 (:DEFINITION LOGIC-FNS-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION TERMP))
 (1 1 (:TYPE-PRESCRIPTION LOGIC-FNSP))
 )
(NO-NILS-IN-TERMP-OF-CDR-OF-ASSOC-EQUAL
 (976 80 (:REWRITE NO-NILS-IN-TERMSP-WHEN-SYMBOL-LISTP))
 (873 43 (:REWRITE NO-NILS-IN-TERMSP-OF-CDR))
 (696 92 (:DEFINITION SYMBOL-LISTP))
 (496 16 (:REWRITE NO-NILS-IN-TERMP-OF-CAR))
 (460 460 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (192 192 (:REWRITE DEFAULT-CAR))
 (184 12 (:REWRITE SYMBOL-LISTP-CDR-ASSOC-EQUAL))
 (166 166 (:REWRITE DEFAULT-CDR))
 (148 12 (:DEFINITION SYMBOL-LIST-LISTP))
 (84 84 (:REWRITE NO-NILS-IN-TERMSP-WHEN-TERM-LISTP))
 (84 84 (:REWRITE NO-NILS-IN-TERMSP-WHEN-LOGIC-TERM-LISTP))
 (60 60 (:TYPE-PRESCRIPTION SYMBOL-LIST-LISTP))
 (25 25 (:REWRITE NO-NILS-IN-TERMP-WHEN-TERMP))
 (25 25 (:REWRITE NO-NILS-IN-TERMP-WHEN-SYMBOLP))
 (25 25 (:REWRITE NO-NILS-IN-TERMP-WHEN-LOGIC-TERMP))
 )
