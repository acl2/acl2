(MERGE-TREE-INTO-DAG-ARRAY-BASIC
 (3802 38 (:DEFINITION INTEGER-ABS))
 (3375 69 (:REWRITE USE-ALL-<-FOR-CAR))
 (3087 42 (:DEFINITION NAT-LISTP))
 (2028 33 (:REWRITE ALL-NATP-OF-CDR))
 (1959 39 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (1926 18 (:REWRITE ALL-<-OF-CDR))
 (1923 66 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (1638 39 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (1089 42 (:DEFINITION NATP))
 (508 213 (:REWRITE DEFAULT-+-2))
 (477 42 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (380 19 (:DEFINITION LENGTH))
 (378 378 (:TYPE-PRESCRIPTION NAT-LISTP))
 (305 213 (:REWRITE DEFAULT-+-1))
 (228 228 (:TYPE-PRESCRIPTION ALL-NATP))
 (228 19 (:DEFINITION LEN))
 (195 195 (:TYPE-PRESCRIPTION ALL-<))
 (138 69 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (132 66 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (128 110 (:REWRITE DEFAULT-<-2))
 (127 127 (:REWRITE USE-ALL-CONSP-2))
 (127 127 (:REWRITE USE-ALL-CONSP))
 (114 110 (:REWRITE DEFAULT-<-1))
 (111 66 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (110 110 (:REWRITE USE-ALL-<=-2))
 (110 110 (:REWRITE USE-ALL-<=))
 (110 110 (:REWRITE USE-ALL-<-2))
 (110 110 (:REWRITE USE-ALL-<))
 (110 110 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (110 110 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (104 104 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (102 51 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (102 51 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (102 51 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (87 6 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (78 3 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (76 38 (:REWRITE LEN-WHEN-DARGP-CHEAP))
 (69 69 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (67 67 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (66 66 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (66 39 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (51 51 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (51 51 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (42 42 (:REWRITE USE-ALL-NATP-2))
 (42 42 (:REWRITE USE-ALL-NATP))
 (42 42 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (42 42 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (42 9 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (42 6 (:REWRITE ALL-RATIONALP-OF-CDR))
 (42 6 (:REWRITE ALL-CONSP-OF-CDR))
 (39 39 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (39 39 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (39 39 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (39 39 (:REWRITE ALL-<-TRANSITIVE))
 (39 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (38 38 (:TYPE-PRESCRIPTION DARGP))
 (38 38 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (38 38 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (38 38 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (38 38 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 6 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (24 24 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (24 24 (:TYPE-PRESCRIPTION ALL-CONSP))
 (24 24 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (24 24 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (19 19 (:TYPE-PRESCRIPTION LEN))
 (19 19 (:REWRITE USE-ALL-RATIONALP-2))
 (19 19 (:REWRITE USE-ALL-RATIONALP))
 (19 19 (:REWRITE DEFAULT-REALPART))
 (19 19 (:REWRITE DEFAULT-NUMERATOR))
 (19 19 (:REWRITE DEFAULT-IMAGPART))
 (19 19 (:REWRITE DEFAULT-DENOMINATOR))
 (19 19 (:REWRITE DEFAULT-COERCE-2))
 (19 19 (:REWRITE DEFAULT-COERCE-1))
 (18 18 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (18 6 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (12 12 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (12 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (6 6 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (6 6 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (6 6 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 )
(FLAG-MERGE-TREE-INTO-DAG-ARRAY-BASIC
 (4608 60 (:DEFINITION INTEGER-ABS))
 (3927 89 (:REWRITE USE-ALL-<-FOR-CAR))
 (3559 54 (:DEFINITION NAT-LISTP))
 (2205 43 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (2153 78 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (2046 35 (:REWRITE ALL-NATP-OF-CDR))
 (1926 18 (:REWRITE ALL-<-OF-CDR))
 (1912 43 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (1301 54 (:DEFINITION NATP))
 (719 315 (:REWRITE DEFAULT-+-2))
 (600 30 (:DEFINITION LENGTH))
 (557 54 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (450 450 (:TYPE-PRESCRIPTION NAT-LISTP))
 (447 315 (:REWRITE DEFAULT-+-1))
 (360 30 (:DEFINITION LEN))
 (266 266 (:TYPE-PRESCRIPTION ALL-NATP))
 (239 239 (:TYPE-PRESCRIPTION ALL-<))
 (178 89 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (174 151 (:REWRITE DEFAULT-<-2))
 (158 151 (:REWRITE DEFAULT-<-1))
 (156 156 (:REWRITE USE-ALL-CONSP-2))
 (156 156 (:REWRITE USE-ALL-CONSP))
 (156 78 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (151 151 (:REWRITE USE-ALL-<=-2))
 (151 151 (:REWRITE USE-ALL-<=))
 (151 151 (:REWRITE USE-ALL-<-2))
 (151 151 (:REWRITE USE-ALL-<))
 (151 151 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (151 151 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (142 142 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (123 78 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (120 60 (:REWRITE LEN-WHEN-DARGP-CHEAP))
 (118 59 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (118 59 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (118 59 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (107 10 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (98 7 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (89 89 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (82 82 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (78 78 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (70 43 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (60 60 (:TYPE-PRESCRIPTION DARGP))
 (60 60 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (60 60 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (60 60 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
 (59 59 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (59 59 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (54 54 (:REWRITE USE-ALL-NATP-2))
 (54 54 (:REWRITE USE-ALL-NATP))
 (54 54 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (48 24 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (48 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (46 46 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (46 13 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (43 43 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (43 43 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (43 43 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (43 43 (:REWRITE ALL-<-TRANSITIVE))
 (43 16 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (42 6 (:REWRITE ALL-RATIONALP-OF-CDR))
 (42 6 (:REWRITE ALL-CONSP-OF-CDR))
 (32 32 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (32 32 (:TYPE-PRESCRIPTION ALL-CONSP))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (30 30 (:REWRITE USE-ALL-RATIONALP-2))
 (30 30 (:REWRITE USE-ALL-RATIONALP))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (26 26 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (24 24 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (24 24 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (24 24 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (18 6 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (16 16 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (13 13 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (10 10 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-MERGE-TREE-INTO-DAG-ARRAY-BASIC-EQUIVALENCES)
(FLAG-LEMMA-FOR-MERGE-TREE-INTO-DAG-ARRAY-BASIC-RETURN-TYPE
 (113182 343 (:REWRITE AXE-TREEP-OF-CAR))
 (47341 1010 (:DEFINITION PSEUDO-TERM-LISTP))
 (44388 24975 (:REWRITE DEFAULT-CAR))
 (41977 629 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (38939 2583 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (36529 512 (:DEFINITION NAT-LISTP))
 (30682 25290 (:REWRITE DEFAULT-CDR))
 (28785 386 (:REWRITE USE-ALL-<-FOR-CAR))
 (28164 687 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (25815 723 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (21531 4521 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (18219 1793 (:DEFINITION MEMBER-EQUAL))
 (17533 17533 (:REWRITE USE-ALL-CONSP-2))
 (17533 17533 (:REWRITE USE-ALL-CONSP))
 (15558 289 (:REWRITE ALL-NATP-OF-CDR))
 (15175 257 (:REWRITE ALL-<-OF-CDR))
 (14192 7096 (:REWRITE LEN-WHEN-DARGP-CHEAP))
 (14153 1948 (:REWRITE ALL-CONSP-OF-CDR))
 (14051 1033 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (13573 2583 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (13354 530 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (11097 530 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (10677 562 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (10048 629 (:REWRITE AXE-TREE-LISTP-WHEN-DARG-LISTP))
 (9056 9056 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (9042 9042 (:TYPE-PRESCRIPTION ALL-CONSP))
 (9041 728 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (8961 8961 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8368 8368 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (8233 4117 (:REWRITE DEFAULT-+-2))
 (7831 7831 (:TYPE-PRESCRIPTION DARGP))
 (7592 7592 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (7096 7096 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (7096 7096 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (7096 7096 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (6748 1082 (:REWRITE DARG-LISTP-OF-CDR))
 (5850 1950 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (4531 4521 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4182 34 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (4117 4117 (:REWRITE DEFAULT-+-1))
 (3967 333 (:REWRITE DARGP-OF-CAR-WHEN-DARG-LISTP))
 (3816 3816 (:TYPE-PRESCRIPTION DARG-LISTP))
 (3816 1908 (:REWRITE DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (3733 625 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (3200 1669 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (3150 3150 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2773 2773 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2760 345 (:DEFINITION ASSOC-KEYWORD))
 (2736 1908 (:REWRITE DARG-LISTP-WHEN-NOT-CONSP))
 (2683 636 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2583 2583 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2583 2583 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2583 2583 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (1965 1965 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1908 1908 (:REWRITE DARG-LISTP-WHEN-BOUNDED-DARG-LISTP))
 (1888 444 (:REWRITE DEFAULT-<-1))
 (1844 520 (:REWRITE DARGP-WHEN-NOT-CONSP-CHEAP))
 (1705 513 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1665 1665 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1605 3 (:REWRITE ALL-<-OF-CONS))
 (1534 1534 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1519 1519 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (1482 42 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1374 687 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (1344 1 (:REWRITE RATIONALP-OF-ALEN1-WHEN-ARRAY1P))
 (1341 1 (:DEFINITION ARRAY1P))
 (1040 1040 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1014 1014 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (988 52 (:DEFINITION STRIP-CDRS))
 (977 977 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (938 444 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (933 933 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (772 386 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (768 384 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (768 384 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (768 384 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (747 687 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (727 727 (:REWRITE USE-ALL-NATP-2))
 (727 727 (:REWRITE USE-ALL-NATP))
 (687 687 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (664 625 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (636 636 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (636 636 (:REWRITE ALL-<-TRANSITIVE))
 (564 564 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (526 526 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (520 520 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (520 520 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (508 444 (:REWRITE DEFAULT-<-2))
 (444 444 (:REWRITE USE-ALL-<-2))
 (444 444 (:REWRITE USE-ALL-<))
 (438 438 (:REWRITE USE-ALL-<=-2))
 (438 438 (:REWRITE USE-ALL-<=))
 (430 215 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (394 215 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (390 390 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (390 390 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (384 384 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (384 384 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (384 384 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (338 33 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-DARG-LISTP))
 (328 164 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (328 164 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (305 3 (:REWRITE ALL-<-OF-REVAPPEND-2))
 (299 299 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (299 299 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (299 299 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (253 1 (:DEFINITION BOUNDED-INTEGER-ALISTP))
 (241 41 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (210 6 (:REWRITE CONSP-OF-TAKE))
 (195 195 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (174 174 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (165 165 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (164 164 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (164 164 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (144 2 (:DEFINITION REVAPPEND))
 (131 1 (:DEFINITION LENGTH))
 (114 57 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (114 57 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (110 1 (:REWRITE NOT-<-OF-CAR-WHEN-ALL-<-2))
 (99 1 (:REWRITE USE-ALL-<=-FOR-CAR))
 (96 6 (:REWRITE ZP-OPEN))
 (87 2 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
 (86 86 (:LINEAR ARRAY2P-LINEAR))
 (66 33 (:REWRITE BOUNDED-AXE-TREEP-WHEN-DARGP-LESS-THAN-CHEAP))
 (66 2 (:REWRITE ALL-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (62 2 (:REWRITE CDR-OF-TAKE))
 (53 9 (:REWRITE ALL-<-OF-TAKE))
 (49 1 (:REWRITE ALL-<=-OF-CDR))
 (46 3 (:REWRITE BOUNDED-INTEGER-ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (40 1 (:REWRITE BOUND-ON-MV-NTH-3-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-WITH-NAME-3-GEN))
 (38 38 (:REWRITE USE-ALL-RATIONALP-2))
 (38 38 (:REWRITE USE-ALL-RATIONALP))
 (38 38 (:REWRITE BOUNDED-AXE-TREEP-MONO))
 (35 1 (:DEFINITION ALISTP))
 (24 1 (:DEFINITION KEYWORD-VALUE-LISTP))
 (21 5 (:REWRITE BOUNDED-NATP-ALISTP-WHEN-PSEUDO-DAGP-GEN))
 (20 10 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (19 14 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (16 16 (:TYPE-PRESCRIPTION PAIRLIS$-FAST-AUX))
 (16 16 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-NTH-0-AND-QUOTE))
 (16 2 (:REWRITE BOUNDED-NATP-ALISTP-OF-CDR))
 (14 10 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (14 10 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (12 12 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (12 12 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (12 12 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (12 10 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONSP-CHEAP))
 (11 1 (:DEFINITION KEYWORDP))
 (10 10 (:TYPE-PRESCRIPTION BOUNDED-NATP-ALISTP))
 (10 4 (:REWRITE SYMBOL-LISTP-OF-TRUE-LIST-FIX))
 (9 3 (:REWRITE DAG-VARIABLE-ALISTP-FORWARD-TO-ALIST))
 (9 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (9 1 (:REWRITE ALISTP-OF-CDR))
 (8 4 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-WITH-NAME))
 (8 2 (:REWRITE CAR-OF-TAKE-STRONG))
 (6 6 (:REWRITE ASSOC-EQUAL-WHEN-PSEUDO-DAGP-AUX))
 (6 6 (:REWRITE ASSOC-EQUAL-WHEN-LOOKUP-EQUAL-CHEAP))
 (5 5 (:REWRITE BOUNDED-NATP-ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE BOUNDED-NATP-ALISTP-MONOTONE))
 (4 4 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (4 4 (:TYPE-PRESCRIPTION ALL-<=))
 (4 2 (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
 (4 1 (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP))
 (3 3 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-LIST))
 (3 3 (:REWRITE BOUNDED-INTEGER-ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE BOUNDED-INTEGER-ALISTP-WHEN-BOUNDED-INTEGER-ALISTP))
 (3 3 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL-ALT))
 (2 2 (:REWRITE ALL-<=-MONOTONE))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (1 1 (:REWRITE ARRAY1P-WHEN-PSEUDO-DAG-ARRAYP))
 )
(MERGE-TREE-INTO-DAG-ARRAY-BASIC-RETURN-TYPE)
(MERGE-TREES-INTO-DAG-ARRAY-BASIC-RETURN-TYPE)
(MERGE-TREE-INTO-DAG-ARRAY-BASIC
 (46155 96 (:REWRITE AXE-TREEP-OF-CAR))
 (43851 22 (:DEFINITION AXE-TREEP))
 (43039 112 (:REWRITE AXE-TREE-LISTP-OF-CDR))
 (38187 112 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (27266 52 (:DEFINITION AXE-TREE-LISTP))
 (18479 7118 (:REWRITE DEFAULT-CAR))
 (14795 937 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (10466 7158 (:REWRITE DEFAULT-CDR))
 (9761 1422 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (7740 250 (:DEFINITION PSEUDO-TERM-LISTP))
 (7238 329 (:DEFINITION ASSOC-EQUAL))
 (6541 172 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (5911 73 (:DEFINITION NAT-LISTP))
 (5804 5804 (:REWRITE USE-ALL-CONSP-2))
 (5804 5804 (:REWRITE USE-ALL-CONSP))
 (5561 487 (:REWRITE ALL-CONSP-OF-CDR))
 (4954 68 (:REWRITE USE-ALL-<-FOR-CAR))
 (4938 49 (:DEFINITION NATP))
 (4595 118 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (4439 366 (:DEFINITION MEMBER-EQUAL))
 (4323 55 (:REWRITE ALL-NATP-OF-CDR))
 (4268 937 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (4085 272 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (3976 1988 (:REWRITE LEN-WHEN-DARGP-CHEAP))
 (3835 91 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (3035 45 (:REWRITE ALL-<-OF-CDR))
 (2930 114 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (2844 2844 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (2844 2844 (:TYPE-PRESCRIPTION ALL-CONSP))
 (2636 2636 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2624 328 (:DEFINITION ASSOC-KEYWORD))
 (2347 172 (:REWRITE AXE-TREE-LISTP-WHEN-DARG-LISTP))
 (2331 1169 (:REWRITE DEFAULT-+-2))
 (2250 85 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (2174 85 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (2153 2153 (:TYPE-PRESCRIPTION DARGP))
 (1988 1988 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (1988 1988 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1988 1988 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (1858 41 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (1843 1843 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1830 1830 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1574 86 (:DEFINITION STRIP-CDRS))
 (1536 138 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (1461 487 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (1453 95 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1422 1422 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1282 106 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1242 206 (:REWRITE DARG-LISTP-OF-CDR))
 (1169 1169 (:REWRITE DEFAULT-+-1))
 (1032 48 (:DEFINITION MYQUOTEP))
 (944 944 (:TYPE-PRESCRIPTION DARG-LISTP))
 (944 472 (:REWRITE DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (937 937 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (937 937 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (937 937 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (816 89 (:REWRITE DARGP-OF-CAR-WHEN-DARG-LISTP))
 (796 48 (:DEFINITION QUOTEP))
 (752 376 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (727 727 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (688 688 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (684 472 (:REWRITE DARG-LISTP-WHEN-NOT-CONSP))
 (582 582 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (521 521 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (472 472 (:REWRITE DARG-LISTP-WHEN-BOUNDED-DARG-LISTP))
 (403 46 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (397 397 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (389 41 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-DARG-LISTP))
 (373 373 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (331 331 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (321 9 (:REWRITE CONSP-OF-TAKE))
 (276 276 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (268 268 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (238 118 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (236 118 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (187 138 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (144 9 (:REWRITE ZP-OPEN))
 (141 141 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (141 141 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (141 141 (:REWRITE ALL-<-TRANSITIVE))
 (136 68 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (124 62 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (124 62 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (124 62 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (118 118 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (116 58 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (116 58 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (116 1 (:REWRITE ALL-<-OF-REVAPPEND-2))
 (114 114 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (114 114 (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP))
 (112 112 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (111 93 (:REWRITE DEFAULT-<-2))
 (107 107 (:REWRITE DARGP-WHEN-NOT-CONSP-CHEAP))
 (107 107 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (107 107 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (98 49 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (98 49 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (95 95 (:REWRITE USE-ALL-NATP-2))
 (95 95 (:REWRITE USE-ALL-NATP))
 (93 93 (:REWRITE USE-ALL-<=-2))
 (93 93 (:REWRITE USE-ALL-<=))
 (93 93 (:REWRITE USE-ALL-<-2))
 (93 93 (:REWRITE USE-ALL-<))
 (93 93 (:REWRITE DEFAULT-<-1))
 (93 93 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (93 93 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (83 41 (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-NOT-CONSP))
 (82 82 (:LINEAR ARRAY2P-LINEAR))
 (75 75 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (72 1 (:DEFINITION REVAPPEND))
 (69 69 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (68 68 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (68 34 (:REWRITE BOUNDED-AXE-TREEP-WHEN-DARGP-LESS-THAN-CHEAP))
 (62 62 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (62 62 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (58 58 (:TYPE-PRESCRIPTION MYQUOTEP))
 (54 27 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (54 27 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (49 49 (:REWRITE BOUNDED-AXE-TREEP-MONO))
 (48 48 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (48 48 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (48 48 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (46 46 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (46 6 (:REWRITE ALL-<-OF-TAKE))
 (38 19 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (34 34 (:TYPE-PRESCRIPTION DARGP-LESS-THAN))
 (31 1 (:REWRITE CDR-OF-TAKE))
 (28 28 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (27 27 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (27 27 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (27 27 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (18 18 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (18 18 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (17 5 (:REWRITE SYMBOL-LISTP-OF-TRUE-LIST-FIX))
 (8 7 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONSP-CHEAP))
 (4 1 (:REWRITE CAR-OF-TAKE-STRONG))
 )
