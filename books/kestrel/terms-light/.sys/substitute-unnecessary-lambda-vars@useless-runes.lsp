(COUNT-FREE-OCCURENCES-IN-TERM
 (495 210 (:REWRITE DEFAULT-+-2))
 (293 210 (:REWRITE DEFAULT-+-1))
 (237 237 (:REWRITE DEFAULT-CDR))
 (128 32 (:DEFINITION INTEGER-ABS))
 (98 2 (:DEFINITION COUNT-FREE-OCCURENCES-IN-TERM))
 (82 41 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (52 37 (:REWRITE DEFAULT-<-2))
 (48 4 (:DEFINITION PSEUDO-TERM-LISTP))
 (41 41 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (41 37 (:REWRITE DEFAULT-<-1))
 (36 18 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (36 18 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (17 17 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (16 8 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (8 4 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (7 1 (:DEFINITION COUNT-FREE-OCCURENCES-IN-TERMS))
 (5 5 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 )
(VARS-THAT-APPEAR-ONLY-ONCE)
(SYMBOL-LISTP-OF-VARS-THAT-APPEAR-ONLY-ONCE
 (282 6 (:DEFINITION COUNT-FREE-OCCURENCES-IN-TERM))
 (64 64 (:REWRITE DEFAULT-CDR))
 (60 12 (:DEFINITION MEMBER-EQUAL))
 (60 6 (:REWRITE COMMUTATIVITY-2-OF-+))
 (54 54 (:REWRITE DEFAULT-CAR))
 (54 24 (:REWRITE DEFAULT-+-2))
 (36 24 (:REWRITE DEFAULT-+-1))
 (24 12 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION COUNT-FREE-OCCURENCES-IN-TERMS))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (12 12 (:TYPE-PRESCRIPTION NON-TRIVIAL-FORMALS))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 12 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (11 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(PAIR-GIVEN-FORMALS-WITH-ARGS
 (191 188 (:REWRITE DEFAULT-CDR))
 (133 130 (:REWRITE DEFAULT-CAR))
 (96 48 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (48 48 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (42 21 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (25 25 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (21 21 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(SYMBOL-TERM-ALISTP-OF-PAIR-GIVEN-FORMALS-WITH-ARGS
 (276 4 (:DEFINITION PSEUDO-TERMP))
 (95 93 (:REWRITE DEFAULT-CAR))
 (90 88 (:REWRITE DEFAULT-CDR))
 (80 12 (:DEFINITION LENGTH))
 (68 12 (:DEFINITION LEN))
 (60 5 (:DEFINITION PSEUDO-TERM-LISTP))
 (32 14 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (28 28 (:TYPE-PRESCRIPTION LEN))
 (24 12 (:REWRITE DEFAULT-+-2))
 (24 8 (:DEFINITION TRUE-LISTP))
 (18 9 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (17 17 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (13 13 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (8 4 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 )
(SYMBOL-ALISTP-OF-PAIR-GIVEN-FORMALS-WITH-ARGS
 (35 33 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (21 20 (:REWRITE DEFAULT-CDR))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (5 5 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 )
(KEEP-ARGS-FOR-NON-DROPPED-FORMALS
 (30 10 (:DEFINITION MEMBER-EQUAL))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 )
(PSEUDO-TERM-LISTP-OF-KEEP-ARGS-FOR-NON-DROPPED-FORMALS
 (59 23 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (26 26 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE DEFAULT-CDR))
 (23 23 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (20 20 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 9 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (9 9 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(LEN-OF-KEEP-ARGS-FOR-NON-DROPPED-FORMALS
 (38 36 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE DEFAULT-+-2))
 (26 26 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE DEFAULT-+-1))
 )
(GET-ARGS-FOR-FORMALS
 (30 10 (:DEFINITION MEMBER-EQUAL))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 )
(PSEUDO-TERM-LISTP-OF-GET-ARGS-FOR-FORMALS
 (59 23 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (26 26 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE DEFAULT-CDR))
 (23 23 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (20 20 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 9 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (9 9 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(VARS-BOUND-TO-THEMSELVES
 (5 5 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:DEFINITION TRUE-LISTP))
 )
(VARS-EXPRESSIBLE-WITHOUT-CLASHES)
(SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM
 (534 225 (:REWRITE DEFAULT-+-2))
 (316 225 (:REWRITE DEFAULT-+-1))
 (160 40 (:DEFINITION INTEGER-ABS))
 (160 20 (:DEFINITION LENGTH))
 (100 20 (:DEFINITION LEN))
 (66 48 (:REWRITE DEFAULT-<-2))
 (54 48 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 20 (:TYPE-PRESCRIPTION LEN))
 (20 20 (:REWRITE DEFAULT-REALPART))
 (20 20 (:REWRITE DEFAULT-NUMERATOR))
 (20 20 (:REWRITE DEFAULT-IMAGPART))
 (20 20 (:REWRITE DEFAULT-DENOMINATOR))
 (20 20 (:REWRITE DEFAULT-COERCE-2))
 (20 20 (:REWRITE DEFAULT-COERCE-1))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(FLAG-SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM
 (808 357 (:REWRITE DEFAULT-+-2))
 (500 357 (:REWRITE DEFAULT-+-1))
 (272 68 (:DEFINITION INTEGER-ABS))
 (272 34 (:DEFINITION LENGTH))
 (170 34 (:DEFINITION LEN))
 (112 84 (:REWRITE DEFAULT-<-2))
 (98 84 (:REWRITE DEFAULT-<-1))
 (72 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (68 68 (:REWRITE DEFAULT-UNARY-MINUS))
 (34 34 (:TYPE-PRESCRIPTION LEN))
 (34 34 (:REWRITE DEFAULT-REALPART))
 (34 34 (:REWRITE DEFAULT-NUMERATOR))
 (34 34 (:REWRITE DEFAULT-IMAGPART))
 (34 34 (:REWRITE DEFAULT-DENOMINATOR))
 (34 34 (:REWRITE DEFAULT-COERCE-2))
 (34 34 (:REWRITE DEFAULT-COERCE-1))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM-EQUIVALENCES)
(FLAG-LEMMA-FOR-PSEUDO-TERMP-OF-SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM
 (9876 6726 (:REWRITE DEFAULT-CDR))
 (7517 5699 (:REWRITE DEFAULT-CAR))
 (4620 231 (:DEFINITION VARS-BOUND-TO-THEMSELVES))
 (4313 865 (:DEFINITION MEMBER-EQUAL))
 (2625 105 (:DEFINITION PAIR-GIVEN-FORMALS-WITH-ARGS))
 (2592 108 (:DEFINITION GET-ARGS-FOR-FORMALS))
 (2494 1247 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2106 162 (:DEFINITION PAIRLIS$))
 (1116 186 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (1012 204 (:DEFINITION TRUE-LIST-FIX))
 (866 866 (:TYPE-PRESCRIPTION VARS-EXPRESSIBLE-WITHOUT-CLASHES))
 (652 326 (:REWRITE DEFAULT-+-2))
 (648 648 (:TYPE-PRESCRIPTION VARS-BOUND-TO-THEMSELVES))
 (386 194 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (330 326 (:REWRITE DEFAULT-+-1))
 (324 324 (:TYPE-PRESCRIPTION VARS-THAT-APPEAR-ONLY-ONCE))
 (261 106 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (110 6 (:REWRITE PSEUDO-TERM-LISTP-OF-SET-DIFFERENCE-EQUAL))
 (105 105 (:DEFINITION ACONS))
 (98 98 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (91 91 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (74 37 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (70 35 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (43 43 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 )
(PSEUDO-TERMP-OF-SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM)
(PSEUDO-TERM-LISTP-OF-SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERMS)
(SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM
 (17017 77 (:DEFINITION SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERM))
 (8592 5856 (:REWRITE DEFAULT-CDR))
 (7309 563 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (6570 4989 (:REWRITE DEFAULT-CAR))
 (4120 206 (:DEFINITION VARS-BOUND-TO-THEMSELVES))
 (3800 762 (:DEFINITION MEMBER-EQUAL))
 (2208 92 (:DEFINITION GET-ARGS-FOR-FORMALS))
 (2175 87 (:DEFINITION PAIR-GIVEN-FORMALS-WITH-ARGS))
 (2116 1058 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1846 142 (:DEFINITION PAIRLIS$))
 (952 192 (:DEFINITION TRUE-LIST-FIX))
 (931 161 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (684 228 (:DEFINITION SUBSTITUTE-UNNECESSARY-LAMBDA-VARS-IN-TERMS))
 (542 271 (:REWRITE DEFAULT-+-2))
 (456 163 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (432 28 (:REWRITE PSEUDO-TERM-LISTP-OF-SET-DIFFERENCE-EQUAL))
 (322 162 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (275 271 (:REWRITE DEFAULT-+-1))
 (105 105 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (87 87 (:DEFINITION ACONS))
 (67 67 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (44 22 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (34 17 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (26 1 (:REWRITE SYMBOL-TERM-ALISTP-OF-PAIRLIS$-ALT))
 )