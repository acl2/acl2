(RSQ
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(APPLY$-WARRANT-RSQ)
(APPLY$-WARRANT-RSQ-DEFINITION)
(APPLY$-WARRANT-RSQ-NECC)
(APPLY$-RSQ
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(ISQ
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(APPLY$-WARRANT-ISQ)
(APPLY$-WARRANT-ISQ-DEFINITION)
(APPLY$-WARRANT-ISQ-NECC)
(APPLY$-ISQ
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(SYMP)
(APPLY$-WARRANT-SYMP)
(APPLY$-WARRANT-SYMP-DEFINITION)
(APPLY$-WARRANT-SYMP-NECC)
(APPLY$-SYMP
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(SSQ)
(APPLY$-WARRANT-SSQ)
(APPLY$-WARRANT-SSQ-DEFINITION)
(APPLY$-WARRANT-SSQ-NECC)
(APPLY$-SSQ
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(FOO
 (1269 5 (:DEFINITION APPLY$-BADGEP))
 (885 5 (:DEFINITION SUBSETP-EQUAL))
 (862 72 (:DEFINITION MEMBER-EQUAL))
 (801 3 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (791 11 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (651 651 (:REWRITE DEFAULT-CDR))
 (568 10 (:DEFINITION NATP))
 (510 35 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (508 11 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (508 2 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-2))
 (295 295 (:REWRITE DEFAULT-CAR))
 (259 7 (:DEFINITION LOOP$-AS))
 (105 105 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (102 18 (:DEFINITION RATIONAL-LISTP))
 (91 14 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (91 14 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (74 36 (:REWRITE DEFAULT-+-2))
 (70 70 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (70 14 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (63 6 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-LISTP-2))
 (58 6 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-LISTP-1))
 (46 46 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (43 36 (:REWRITE DEFAULT-+-1))
 (40 20 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (40 4 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-2))
 (37 37 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (36 6 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-2))
 (36 4 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-1))
 (36 2 (:DEFINITION ALWAYS$))
 (32 8 (:DEFINITION INTEGER-LISTP))
 (32 4 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (31 6 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (30 5 (:DEFINITION ALL-NILS))
 (26 26 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
 (23 4 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (21 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (20 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (20 4 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (20 2 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (17 17 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (16 4 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-2))
 (14 2 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-1))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (12 12 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (12 4 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (11 5 (:REWRITE DEFAULT-*-2))
 (10 10 (:TYPE-PRESCRIPTION ALWAYS$))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 2 (:REWRITE APPLY$-PRIMITIVE))
 (9 5 (:REWRITE DEFAULT-*-1))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (8 8 (:REWRITE APPLY$-WARRANT-SSQ-NECC))
 (8 8 (:REWRITE APPLY$-WARRANT-RSQ-NECC))
 (8 8 (:REWRITE APPLY$-WARRANT-ISQ-NECC))
 (8 4 (:REWRITE APPLY$-PRIMP-BADGE))
 (6 6 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (6 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (6 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (6 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 (4 4 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (2 2 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (2 2 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE APPLY$-CONSP-ARITY-1))
 (2 2 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (2 2 (:DEFINITION IDENTITY))
 )
(TRUE-LISTP-MAKE-LIST-AC
 (13 11 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(INTEGER-LISTP-MAKE-LIST-AC
 (13 13 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (12 10 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ACL2-NUMBER-LISTP-MAKE-LIST-AC
 (32 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 13 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (13 13 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (12 10 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(RATIONAL-LISTP-MAKE-LIST-AC
 (14 10 (:REWRITE DEFAULT-CDR))
 (14 10 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(TEST)
(TEST
 (30182 130 (:DEFINITION APPLY$-BADGEP))
 (20886 118 (:DEFINITION SUBSETP-EQUAL))
 (16287 61 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (16172 270 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (14771 276 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (14219 14207 (:REWRITE DEFAULT-CDR))
 (12036 826 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (11430 45 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-2))
 (5626 5614 (:REWRITE DEFAULT-CAR))
 (2478 2478 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (2244 581 (:DEFINITION MAKE-LIST-AC))
 (2076 1426 (:REWRITE DEFAULT-+-2))
 (1758 293 (:DEFINITION TAILS))
 (1652 1652 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (1464 1426 (:REWRITE DEFAULT-+-1))
 (1424 130 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (1125 1125 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (1023 28 (:DEFINITION UNTIL$+))
 (996 850 (:REWRITE DEFAULT-<-2))
 (944 472 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (883 850 (:REWRITE DEFAULT-<-1))
 (708 118 (:DEFINITION ALL-NILS))
 (674 674 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (590 590 (:TYPE-PRESCRIPTION ALL-NILS))
 (552 18 (:DEFINITION ALWAYS$))
 (536 15 (:DEFINITION UNTIL$))
 (520 130 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (509 509 (:REWRITE ZP-OPEN))
 (472 472 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (455 6 (:DEFINITION WHEN$+))
 (431 29 (:REWRITE APPLY$-CONSP-ARITY-1))
 (413 70 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (405 207 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (323 17 (:REWRITE NOT-MEMBER-TAILS-TRUE-LIST-LISTP))
 (315 45 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-1))
 (292 67 (:REWRITE APPLY$-PRIMITIVE))
 (256 14 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (255 17 (:REWRITE NOT-MEMBER-TAILS-ACL2-NUMBER-LISTP))
 (238 17 (:REWRITE NOT-MEMBER-TAILS-SYMBOL-LISTP))
 (221 17 (:REWRITE NOT-MEMBER-TAILS-RATIONAL-LISTP))
 (221 17 (:REWRITE NOT-MEMBER-TAILS-INTEGER-LISTP))
 (210 70 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (188 188 (:TYPE-PRESCRIPTION LOOP$-AS))
 (187 17 (:DEFINITION SYMBOL-LISTP))
 (183 61 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (172 172 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (171 171 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (158 79 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (158 79 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (158 14 (:META APPLY$-PRIM-META-FN-CORRECT))
 (153 17 (:DEFINITION ACL2-NUMBER-LISTP))
 (95 95 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (74 74 (:META RELINK-FANCY-SCION-CORRECT))
 (56 28 (:REWRITE APPLY$-PRIMP-BADGE))
 (48 48 (:REWRITE DEFAULT-*-2))
 (48 48 (:REWRITE DEFAULT-*-1))
 (45 45 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (45 45 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (45 45 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (42 42 (:TYPE-PRESCRIPTION UNTIL$+))
 (38 14 (:DEFINITION IDENTITY))
 (33 33 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 8 (:REWRITE DEFAULT-SYMBOL-NAME))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 )
(BOOHOO
 (2529 10 (:DEFINITION APPLY$-BADGEP))
 (1787 147 (:DEFINITION MEMBER-EQUAL))
 (1770 10 (:DEFINITION SUBSETP-EQUAL))
 (1367 7 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (1322 21 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (1321 7 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-2))
 (1275 1269 (:REWRITE DEFAULT-CDR))
 (1264 21 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (1020 70 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (495 495 (:REWRITE DEFAULT-CAR))
 (354 59 (:DEFINITION TAILS))
 (236 59 (:DEFINITION MAKE-LIST-AC))
 (210 210 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (197 128 (:REWRITE DEFAULT-+-2))
 (140 140 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (128 128 (:REWRITE DEFAULT-+-1))
 (112 14 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (104 9 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-2))
 (102 63 (:REWRITE DEFAULT-<-2))
 (98 1 (:DEFINITION WHEN$+))
 (89 89 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (80 40 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (71 71 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (66 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (63 63 (:REWRITE DEFAULT-<-1))
 (60 10 (:DEFINITION ALL-NILS))
 (59 59 (:REWRITE ZP-OPEN))
 (59 59 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (52 7 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-2))
 (52 7 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-2))
 (51 7 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-1))
 (50 50 (:TYPE-PRESCRIPTION ALL-NILS))
 (46 23 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (40 10 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (37 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (31 16 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (26 2 (:DEFINITION NAT-LISTP))
 (23 23 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (23 7 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (23 7 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (23 7 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-1))
 (22 2 (:DEFINITION ACL2-NUMBER-LISTP))
 (18 2 (:DEFINITION SYMBOL-LISTP))
 (18 2 (:DEFINITION INTEGER-LISTP))
 (14 14 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (14 14 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (12 6 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (10 10 (:TYPE-PRESCRIPTION NAT-LISTP))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (10 10 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (8 2 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (7 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (7 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (3 3 (:META RELINK-FANCY-SCION-CORRECT))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 (1 1 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 )
(BOOHOO-LEMMA
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(BOOHOO
 (1512 6 (:DEFINITION APPLY$-BADGEP))
 (1062 6 (:DEFINITION SUBSETP-EQUAL))
 (1047 87 (:DEFINITION MEMBER-EQUAL))
 (801 3 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (792 12 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (782 782 (:REWRITE DEFAULT-CDR))
 (762 3 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-2))
 (753 12 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (612 42 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (294 294 (:REWRITE DEFAULT-CAR))
 (288 48 (:DEFINITION TAILS))
 (192 48 (:DEFINITION MAKE-LIST-AC))
 (134 91 (:REWRITE DEFAULT-+-2))
 (126 126 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (98 1 (:DEFINITION WHEN$+))
 (91 91 (:REWRITE DEFAULT-+-1))
 (84 84 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (61 38 (:REWRITE DEFAULT-<-2))
 (51 51 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (48 48 (:REWRITE ZP-OPEN))
 (48 24 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (48 6 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (41 41 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (38 38 (:REWRITE DEFAULT-<-1))
 (36 6 (:DEFINITION ALL-NILS))
 (34 34 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (30 30 (:TYPE-PRESCRIPTION ALL-NILS))
 (28 14 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (24 24 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (24 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (22 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (21 3 (:REWRITE NOT-MEMBER-LOOP$-AS-NATP-1))
 (20 12 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (18 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (15 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (12 3 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-2))
 (12 3 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-2))
 (11 11 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-1))
 (6 6 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (6 6 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (6 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (6 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (3 3 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (3 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (3 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (3 3 (:META RELINK-FANCY-SCION-CORRECT))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 (1 1 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 )
(MY-MV)
(APPLY$-WARRANT-MY-MV)
(APPLY$-WARRANT-MY-MV-DEFINITION)
(APPLY$-WARRANT-MY-MV-NECC)
(APPLY$-MY-MV
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(LOOP-WITH-MY-MV-TARGET
 (4 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(BELOW-3P)
(BUG1
 (40 11 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (12 2 (:DEFINITION TRUE-LISTP))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (11 11 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:REWRITE BOOHOO-LEMMA))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(BUG2
 (108 9 (:DEFINITION TRUE-LIST-LISTP))
 (84 4 (:DEFINITION MEMBER-EQUAL))
 (81 8 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (75 5 (:REWRITE NOT-MEMBER-TAILS-TRUE-LIST-LISTP))
 (51 10 (:DEFINITION TRUE-LISTP))
 (50 5 (:REWRITE NOT-MEMBER-TAILS-SYMBOL-LISTP))
 (49 49 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (47 47 (:REWRITE DEFAULT-CDR))
 (41 41 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:REWRITE DEFAULT-CAR))
 (35 5 (:DEFINITION SYMBOL-LISTP))
 (30 5 (:REWRITE NOT-MEMBER-TAILS-ACL2-NUMBER-LISTP))
 (26 5 (:REWRITE NOT-MEMBER-TAILS-RATIONAL-LISTP))
 (25 25 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (18 2 (:DEFINITION ACL2-NUMBER-LISTP))
 (14 2 (:DEFINITION RATIONAL-LISTP))
 (12 12 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (10 5 (:DEFINITION TAILS))
 (8 8 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (5 5 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (4 4 (:REWRITE TRUE-LIST-LISTP-TAILS))
 (4 4 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE BOOHOO-LEMMA))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
(BELOW-11P)
(BUG3)
(LOOP-TEST-1-USING-MY-MV)
(LOOP-TEST-2-USING-MY-MV)
