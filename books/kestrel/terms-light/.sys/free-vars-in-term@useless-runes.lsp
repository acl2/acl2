(FREE-VARS-IN-TERM
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(FLAG-FREE-VARS-IN-TERM
 (216 104 (:REWRITE DEFAULT-+-2))
 (145 104 (:REWRITE DEFAULT-+-1))
 (88 22 (:REWRITE COMMUTATIVITY-OF-+))
 (88 22 (:DEFINITION INTEGER-ABS))
 (88 11 (:DEFINITION LENGTH))
 (55 11 (:DEFINITION LEN))
 (32 32 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (29 25 (:REWRITE DEFAULT-<-2))
 (28 25 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 21 (:REWRITE DEFAULT-CAR))
 (11 11 (:TYPE-PRESCRIPTION LEN))
 (11 11 (:REWRITE DEFAULT-REALPART))
 (11 11 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-IMAGPART))
 (11 11 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-FREE-VARS-IN-TERM-EQUIVALENCES)
(FLAG-LEMMA-FOR-SYMBOL-LISTP-OF-FREE-VARS-IN-TERM
 (362 235 (:REWRITE DEFAULT-CDR))
 (357 230 (:REWRITE DEFAULT-CAR))
 (135 27 (:DEFINITION LEN))
 (113 48 (:REWRITE CONSP-OF-UNION-EQUAL))
 (63 63 (:TYPE-PRESCRIPTION LEN))
 (54 35 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (54 27 (:REWRITE DEFAULT-+-2))
 (37 37 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (35 35 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (27 27 (:REWRITE DEFAULT-+-1))
 (18 9 (:DEFINITION TRUE-LISTP))
 (10 2 (:DEFINITION MEMBER-EQUAL))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 )
(SYMBOL-LISTP-OF-FREE-VARS-IN-TERM)
(SYMBOL-LISTP-OF-FREE-VARS-IN-TERMS)
(FREE-VARS-IN-TERM
 (36 36 (:REWRITE DEFAULT-CDR))
 (35 35 (:REWRITE DEFAULT-CAR))
 (30 6 (:DEFINITION LEN))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (12 12 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 2 (:DEFINITION TRUE-LISTP))
 )
(FLAG-LEMMA-FOR-TRUE-LISTP-OF-FREE-VARS-IN-TERM)
(TRUE-LISTP-OF-FREE-VARS-IN-TERM)
(TRUE-LISTP-OF-FREE-VARS-IN-TERMS)
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-OF-CAR
 (10 5 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (10 5 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (7 7 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (4 2 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (4 2 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (3 3 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 )
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR
 (16 8 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (16 8 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (8 8 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (4 2 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (4 2 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (4 2 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (3 3 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 )
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CAR-CHAIN
 (7 1 (:DEFINITION FREE-VARS-IN-TERMS))
 (4 2 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (2 1 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2 1 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (2 1 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (1 1 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (1 1 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR-CHAIN
 (14 2 (:DEFINITION FREE-VARS-IN-TERMS))
 (4 2 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (4 2 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (4 2 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (2 1 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (1 1 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (1 1 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 )
(FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP)
(FREE-VARS-IN-TERM-WHEN-QUOTEP
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 )
(FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP
 (31 31 (:REWRITE DEFAULT-CAR))
 (10 10 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE UNION-EQUAL-IFF))
 (8 4 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (8 4 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (4 4 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 )
(FREE-VARS-IN-TERM-OF-CONS
 (33 3 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (24 3 (:DEFINITION QUOTE-LISTP))
 (15 15 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (9 4 (:DEFINITION QUOTEP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (5 1 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 (1 1 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 )
(FREE-VARS-IN-TERMS-OF-CONS
 (76 6 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (59 7 (:DEFINITION QUOTE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (24 12 (:DEFINITION QUOTEP))
 (23 23 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 5 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (10 5 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION QUOTEP))
 (5 5 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 )
(FREE-VARS-IN-TERMS-OF-TRUE-LIST-FIX
 (312 27 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (238 27 (:DEFINITION QUOTE-LISTP))
 (125 125 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (93 39 (:DEFINITION QUOTEP))
 (91 91 (:REWRITE DEFAULT-CAR))
 (60 16 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (49 49 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (32 16 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (16 16 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (13 13 (:TYPE-PRESCRIPTION QUOTEP))
 )
(FREE-VARS-IN-TERMS-OF-APPEND
 (640 43 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (516 44 (:DEFINITION QUOTE-LISTP))
 (210 210 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (200 64 (:DEFINITION QUOTEP))
 (178 142 (:REWRITE DEFAULT-CAR))
 (144 72 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (111 75 (:REWRITE DEFAULT-CDR))
 (105 24 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (72 72 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (72 72 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (66 33 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (24 24 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (21 21 (:TYPE-PRESCRIPTION QUOTEP))
 )
(FLAG-LEMMA-FOR-NO-DUPLICATESP-OF-FREE-VARS-IN-TERM
 (158 14 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (118 15 (:DEFINITION QUOTE-LISTP))
 (118 13 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NO-DUPLICATESP-EQUAL-OF-CDR))
 (68 68 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (63 57 (:REWRITE DEFAULT-CAR))
 (51 36 (:REWRITE DEFAULT-CDR))
 (44 44 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (23 5 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CDR))
 (22 11 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (12 6 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (12 6 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (5 5 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (5 5 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 )
(NO-DUPLICATESP-OF-FREE-VARS-IN-TERM)
(NO-DUPLICATESP-OF-FREE-VARS-IN-TERMS)
(FLAG-LEMMA-FOR-FREE-VARS-IN-TERMS-WHEN-SYMBOL-LISTP
 (956 90 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (828 82 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (684 37 (:DEFINITION MEMBER-EQUAL))
 (596 77 (:DEFINITION QUOTE-LISTP))
 (528 12 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR-CHAIN))
 (369 369 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (336 336 (:REWRITE DEFAULT-CAR))
 (248 248 (:REWRITE DEFAULT-CDR))
 (225 118 (:DEFINITION QUOTEP))
 (157 41 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (143 143 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (100 22 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-WHEN-NOT-MEMBER-EQUAL-OF-CAR))
 (98 49 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (90 90 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 (90 6 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG1))
 (72 36 (:REWRITE REMOVE-DUPLICATES-EQUAL-WHEN-NO-DUPLICATESP-EQUAL-CHEAP))
 (64 32 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (64 32 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (48 32 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (41 41 (:TYPE-PRESCRIPTION QUOTEP))
 (40 32 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (36 36 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (34 34 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (32 32 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (32 32 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 )
(FREE-VARS-IN-TERMS-WHEN-SYMBOL-LISTP)
(FREE-VARS-IN-TERMS-WHEN-NOT-CONSP-CHEAP
 (4 1 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (2 1 (:DEFINITION QUOTE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(FLAG-ALL-VARS1
 (216 104 (:REWRITE DEFAULT-+-2))
 (145 104 (:REWRITE DEFAULT-+-1))
 (88 22 (:REWRITE COMMUTATIVITY-OF-+))
 (88 22 (:DEFINITION INTEGER-ABS))
 (88 11 (:DEFINITION LENGTH))
 (55 11 (:DEFINITION LEN))
 (32 32 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (29 25 (:REWRITE DEFAULT-<-2))
 (28 25 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 21 (:REWRITE DEFAULT-CAR))
 (11 11 (:TYPE-PRESCRIPTION LEN))
 (11 11 (:REWRITE DEFAULT-REALPART))
 (11 11 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-IMAGPART))
 (11 11 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (8 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (6 6 (:TYPE-PRESCRIPTION ADD-TO-SET-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-ALL-VARS1-EQUIVALENCES)
(FLAG-LEMMA-FOR-THEOREM-FOR-ALL-VARS1
 (3745 328 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (2852 338 (:DEFINITION QUOTE-LISTP))
 (1579 1579 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (1270 1270 (:REWRITE DEFAULT-CAR))
 (822 411 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (659 659 (:REWRITE DEFAULT-CDR))
 (430 215 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (420 215 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (406 207 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (380 215 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (353 353 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (350 350 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (299 5 (:REWRITE SUBSETP-EQUAL-OF-ALL-VARS1-LST-WHEN-SUBSETP-EQUAL-ARG2))
 (72 24 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-UNION-EQUAL-TYPE))
 (30 6 (:DEFINITION MEMBER-EQUAL))
 (24 24 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (23 23 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (12 12 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 (11 1 (:REWRITE SUBSETP-EQUAL-OF-ALL-VARS1-WHEN-SUBSETP-EQUAL-ARG2))
 )
(THEOREM-FOR-ALL-VARS1)
(THEOREM-FOR-ALL-VARS1-LST)
(SUBSETP-EQUAL-OF-ALL-VARS1-OF-NIL-AND-FREE-VARS-IN-TERM)
(SUBSETP-EQUAL-OF-ALL-VARS-AND-FREE-VARS-IN-TERM)
(FLAG-LEMMA-FOR-SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-AND-ALL-VARS1-HELPER
 (1574 163 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (1164 140 (:DEFINITION QUOTE-LISTP))
 (667 667 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (558 558 (:REWRITE DEFAULT-CAR))
 (412 206 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (301 301 (:REWRITE DEFAULT-CDR))
 (246 123 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (205 105 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (202 123 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (187 123 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (173 173 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (168 168 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (25 5 (:DEFINITION MEMBER-EQUAL))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 (6 2 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-UNION-EQUAL-TYPE))
 (2 2 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-AND-ALL-VARS1-HELPER)
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-AND-ALL-VARS1-LST-HELPER)
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-AND-ALL-VARS1)
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-AND-ALL-VARS)
(SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-AND-FREE-VARS-IN-TERMS-WHEN-MEMBER-EQUAL
 (68 7 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (52 6 (:DEFINITION QUOTE-LISTP))
 (29 29 (:REWRITE DEFAULT-CAR))
 (27 27 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (22 11 (:DEFINITION QUOTEP))
 (20 5 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (12 6 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (8 8 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 (7 7 (:REWRITE FREE-VARS-IN-TERMS-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 (6 3 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (6 3 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (6 3 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION QUOTEP))
 (5 5 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (3 3 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 )
(SET-DIFFERENCE-EQUAL-OF-ALL-VARS-ARG1-IFF
 (12 6 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (8 4 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (8 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (6 4 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (4 4 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (4 4 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (4 2 (:DEFINITION QUOTEP))
 (3 3 (:REWRITE SET-DIFFERENCE-EQUAL-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION QUOTEP))
 (2 2 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (2 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(SET-DIFFERENCE-EQUAL-OF-ALL-VARS-ARG2-IFF
 (14 7 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (11 2 (:REWRITE SUBSETP-EQUAL-OF-ALL-VARS1-WHEN-SUBSETP-EQUAL-ARG2))
 (10 5 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (9 3 (:REWRITE SET-DIFFERENCE-EQUAL-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (8 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (7 7 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 (6 4 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (4 4 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (4 2 (:DEFINITION QUOTEP))
 (2 2 (:TYPE-PRESCRIPTION QUOTEP))
 (2 2 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE SUBSETP-EQUAL-OF-NIL-ARG2))
 )
