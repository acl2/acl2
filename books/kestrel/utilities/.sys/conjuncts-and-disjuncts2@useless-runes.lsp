(NEGATE-TERM2
 (1277 621 (:REWRITE DEFAULT-+-2))
 (1230 117 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (835 621 (:REWRITE DEFAULT-+-1))
 (480 120 (:REWRITE COMMUTATIVITY-OF-+))
 (480 120 (:DEFINITION INTEGER-ABS))
 (402 3 (:DEFINITION PSEUDO-TERMP))
 (361 248 (:REWRITE DEFAULT-<-2))
 (353 67 (:REWRITE LEN-OF-CDR))
 (285 69 (:DEFINITION LENGTH))
 (264 248 (:REWRITE DEFAULT-<-1))
 (180 180 (:REWRITE FOLD-CONSTS-IN-+))
 (142 56 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (120 120 (:REWRITE DEFAULT-UNARY-MINUS))
 (117 117 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (114 114 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (86 21 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (63 63 (:REWRITE DEFAULT-COERCE-2))
 (63 63 (:REWRITE DEFAULT-COERCE-1))
 (60 60 (:REWRITE DEFAULT-REALPART))
 (60 60 (:REWRITE DEFAULT-NUMERATOR))
 (60 60 (:REWRITE DEFAULT-IMAGPART))
 (60 60 (:REWRITE DEFAULT-DENOMINATOR))
 (48 6 (:DEFINITION TRUE-LISTP))
 (47 47 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (42 3 (:DEFINITION SYMBOL-LISTP))
 (13 13 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (11 11 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (10 5 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (6 3 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (6 3 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (6 3 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (6 3 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (4 4 (:REWRITE EQUAL-OF-LEN-AND-0))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(PSEUDO-TERMP-OF-NEGATE-TERM2
 (1969 143 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (662 374 (:REWRITE DEFAULT-CDR))
 (417 417 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (322 23 (:DEFINITION SYMBOL-LISTP))
 (293 33 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (227 131 (:REWRITE DEFAULT-+-2))
 (222 120 (:REWRITE DEFAULT-<-2))
 (143 143 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (138 69 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (131 131 (:REWRITE DEFAULT-+-1))
 (120 120 (:REWRITE DEFAULT-<-1))
 (120 120 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (66 33 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (63 63 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (58 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (50 16 (:REWRITE +-COMBINE-CONSTANTS))
 (46 46 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (45 45 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (40 20 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (36 36 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (20 20 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(LOGIC-TERMP-OF-NEGATE-TERM2
 (751 165 (:REWRITE DEFAULT-CDR))
 (712 64 (:REWRITE LOGIC-TERMP-WHEN-QUOTEP))
 (590 58 (:DEFINITION QUOTEP))
 (357 357 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (136 73 (:REWRITE DEFAULT-<-2))
 (84 14 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (82 82 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (82 82 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (81 81 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (73 73 (:REWRITE DEFAULT-<-1))
 (73 73 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (63 47 (:REWRITE DEFAULT-+-2))
 (58 58 (:TYPE-PRESCRIPTION QUOTEP))
 (47 47 (:REWRITE DEFAULT-+-1))
 (30 30 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (28 8 (:REWRITE +-COMBINE-CONSTANTS))
 (15 15 (:REWRITE ARITIES-OKP-WHEN-ARITIES-OKP-AND-SUBSETP-EQUAL))
 (12 12 (:REWRITE EQUAL-OF-LEN-AND-0))
 )
(NON-TRIVIAL-LOGICAL-TERMP-OF-NEGATE-TERM2
 (4371 240 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (2668 730 (:REWRITE DEFAULT-CDR))
 (727 727 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (593 73 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (482 319 (:REWRITE DEFAULT-+-2))
 (404 222 (:REWRITE DEFAULT-<-2))
 (319 319 (:REWRITE DEFAULT-+-1))
 (252 18 (:DEFINITION SYMBOL-LISTP))
 (240 240 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (222 222 (:REWRITE DEFAULT-<-1))
 (222 222 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (220 66 (:REWRITE +-COMBINE-CONSTANTS))
 (172 86 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (127 127 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (116 58 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (106 53 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (78 78 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (73 73 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (69 69 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (36 36 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (18 18 (:REWRITE DEFAULT-COERCE-2))
 (18 18 (:REWRITE DEFAULT-COERCE-1))
 )
(NEGATE-TERMS2)
(LOGIC-TERM-LISTP-OF-NEGATE-TERMS2
 (56 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (15 15 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (15 15 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (15 15 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (10 6 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 1 (:REWRITE LOGIC-TERMP-WHEN-CONSP))
 (9 9 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(PSEUDO-TERM-LISTP-OF-NEGATE-TERMS2
 (107 10 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (32 16 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (20 10 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (15 11 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (15 10 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (12 6 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (12 6 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (10 10 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(NON-TRIVIAL-LOGICAL-TERM-LISTP-OF-NEGATE-TERMS2
 (10221 632 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5943 1521 (:REWRITE DEFAULT-CDR))
 (1672 1653 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1445 167 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (1122 580 (:REWRITE DEFAULT-<-2))
 (982 565 (:REWRITE DEFAULT-+-2))
 (728 52 (:DEFINITION SYMBOL-LISTP))
 (632 632 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (580 580 (:REWRITE DEFAULT-<-1))
 (580 580 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (565 565 (:REWRITE DEFAULT-+-1))
 (332 94 (:REWRITE +-COMBINE-CONSTANTS))
 (249 249 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (240 120 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (184 92 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (174 87 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (141 141 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (106 106 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (104 104 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (103 103 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (52 52 (:REWRITE DEFAULT-COERCE-2))
 (52 52 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:TYPE-PRESCRIPTION QUOTEP))
 )
(NEGATE-DISJUNCTS)
(PSEUDO-TERM-LISTP-OF-NEGATE-DISJUNCTS
 (58 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (22 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (8 4 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (6 6 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION NEGATE-TERMS2))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 2 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(LOGIC-TERM-LISTP-OF-NEGATE-DISJUNCTS
 (12 12 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (12 12 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (12 12 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 )
(CONJUNCT-LISTP-OF-NEGATE-DISJUNCTS)
(NEGATE-CONJUNCTS)
(DISJUNCT-LISTP-OF-NEGATE-CONJUNCTS)
(PSEUDO-TERM-LISTP-OF-NEGATE-CONJUNCTS
 (58 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (22 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (8 4 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (6 6 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION NEGATE-TERMS2))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 2 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(LOGIC-TERM-LISTP-OF-NEGATE-CONJUNCTS
 (12 12 (:REWRITE ARITY-WHEN-ARITIES-OKP))
 (12 12 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (12 12 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 )
(GET-CONJUNCTS-OF-TERM2
 (8311 4184 (:REWRITE DEFAULT-+-2))
 (7734 720 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5544 4184 (:REWRITE DEFAULT-+-1))
 (3088 772 (:DEFINITION INTEGER-ABS))
 (2406 465 (:REWRITE LEN-OF-CDR))
 (2221 1609 (:REWRITE DEFAULT-<-2))
 (1749 1609 (:REWRITE DEFAULT-<-1))
 (1544 386 (:DEFINITION LENGTH))
 (1102 1102 (:REWRITE FOLD-CONSTS-IN-+))
 (1067 401 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (772 772 (:REWRITE DEFAULT-UNARY-MINUS))
 (720 720 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (720 720 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (386 386 (:REWRITE DEFAULT-REALPART))
 (386 386 (:REWRITE DEFAULT-NUMERATOR))
 (386 386 (:REWRITE DEFAULT-IMAGPART))
 (386 386 (:REWRITE DEFAULT-DENOMINATOR))
 (386 386 (:REWRITE DEFAULT-COERCE-2))
 (386 386 (:REWRITE DEFAULT-COERCE-1))
 (354 354 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (162 81 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (81 81 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(FLAG-GET-CONJUNCTS-OF-TERM2
 (9248 4644 (:REWRITE DEFAULT-+-2))
 (8808 805 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (6149 4644 (:REWRITE DEFAULT-+-1))
 (3384 846 (:DEFINITION INTEGER-ABS))
 (2844 549 (:REWRITE LEN-OF-CDR))
 (2455 1779 (:REWRITE DEFAULT-<-2))
 (1929 1779 (:REWRITE DEFAULT-<-1))
 (1692 423 (:DEFINITION LENGTH))
 (1238 1238 (:REWRITE FOLD-CONSTS-IN-+))
 (1198 442 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (846 846 (:REWRITE DEFAULT-UNARY-MINUS))
 (805 805 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (805 805 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (423 423 (:REWRITE DEFAULT-REALPART))
 (423 423 (:REWRITE DEFAULT-NUMERATOR))
 (423 423 (:REWRITE DEFAULT-IMAGPART))
 (423 423 (:REWRITE DEFAULT-DENOMINATOR))
 (423 423 (:REWRITE DEFAULT-COERCE-2))
 (423 423 (:REWRITE DEFAULT-COERCE-1))
 (402 402 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (198 99 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (99 99 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-GET-CONJUNCTS-OF-TERM2-EQUIVALENCES)
(FLAG-LEMMA-FOR-PSEUDO-TERM-LISTP-OF-GET-CONJUNCTS-OF-TERM2
 (73497 3468 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (62466 9480 (:REWRITE DEFAULT-CDR))
 (13485 1728 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (12277 12162 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8434 6122 (:REWRITE DEFAULT-+-2))
 (6122 6122 (:REWRITE DEFAULT-+-1))
 (5581 3359 (:REWRITE DEFAULT-<-2))
 (3359 3359 (:REWRITE DEFAULT-<-1))
 (3359 3359 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2776 2776 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (1744 1744 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1526 109 (:DEFINITION SYMBOL-LISTP))
 (1516 758 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (1447 1447 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (1242 621 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (1238 619 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (890 445 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (717 717 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (553 553 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (218 218 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (109 109 (:REWRITE DEFAULT-COERCE-2))
 (109 109 (:REWRITE DEFAULT-COERCE-1))
 (80 40 (:TYPE-PRESCRIPTION COMBINE-DISJUNCTS))
 (56 28 (:TYPE-PRESCRIPTION COMBINE-CONJUNCTS))
 )
(PSEUDO-TERM-LISTP-OF-GET-CONJUNCTS-OF-TERM2)
(PSEUDO-TERM-LISTP-OF-GET-DISJUNCTS-OF-TERM2)
(FLAG-LEMMA-FOR-CONJUNCT-LISTP-OF-GET-CONJUNCTS-OF-TERM2
 (72287 3370 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (62368 9382 (:REWRITE DEFAULT-CDR))
 (13485 1728 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (12064 12064 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8434 6122 (:REWRITE DEFAULT-+-2))
 (6122 6122 (:REWRITE DEFAULT-+-1))
 (5385 3261 (:REWRITE DEFAULT-<-2))
 (3261 3261 (:REWRITE DEFAULT-<-1))
 (3261 3261 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2776 2776 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (1744 1744 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1526 109 (:DEFINITION SYMBOL-LISTP))
 (1447 1447 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (1046 523 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (1046 523 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (1042 521 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (694 347 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (521 521 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (455 455 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (218 218 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (109 109 (:REWRITE DEFAULT-COERCE-2))
 (109 109 (:REWRITE DEFAULT-COERCE-1))
 )
(CONJUNCT-LISTP-OF-GET-CONJUNCTS-OF-TERM2)
(DISJUNCT-LISTP-OF-GET-DISJUNCTS-OF-TERM2)
(FLAG-LEMMA-FOR-TRUE-LISTP-OF-GET-CONJUNCTS-OF-TERM2
 (30784 2708 (:REWRITE DEFAULT-CDR))
 (26419 1121 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (12185 1624 (:REWRITE LEN-OF-CDR))
 (5824 679 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (3686 3650 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2626 1624 (:REWRITE DEFAULT-+-2))
 (2064 1121 (:REWRITE DEFAULT-<-2))
 (1624 1624 (:REWRITE DEFAULT-+-1))
 (1374 315 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (1131 315 (:REWRITE +-COMBINE-CONSTANTS))
 (1121 1121 (:REWRITE DEFAULT-<-1))
 (1121 1121 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1121 1121 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (994 994 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (816 816 (:REWRITE EQUAL-OF-LEN-AND-0))
 (648 36 (:DEFINITION TRUE-LISTP))
 (501 315 (:DEFINITION FIX))
 (315 315 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(TRUE-LISTP-OF-GET-CONJUNCTS-OF-TERM2)
(TRUE-LISTP-OF-GET-DISJUNCTS-OF-TERM2)
(GET-CONJUNCTS-OF-TERM2
 (6390 36 (:DEFINITION PSEUDO-TERMP))
 (5492 405 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (4206 818 (:REWRITE DEFAULT-CDR))
 (2663 491 (:REWRITE LEN-OF-CDR))
 (1752 8 (:REWRITE DISJUNCT-LISTP-OF-GET-DISJUNCTS-OF-TERM2))
 (1440 184 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (1314 6 (:REWRITE CONJUNCT-LISTP-OF-GET-CONJUNCTS-OF-TERM2))
 (1204 1200 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (982 186 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (684 72 (:DEFINITION TRUE-LISTP))
 (678 270 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (631 491 (:REWRITE DEFAULT-+-2))
 (570 108 (:DEFINITION LENGTH))
 (558 36 (:DEFINITION SYMBOL-LISTP))
 (515 369 (:REWRITE DEFAULT-<-2))
 (491 491 (:REWRITE DEFAULT-+-1))
 (438 2 (:REWRITE PSEUDO-TERM-LISTP-OF-GET-DISJUNCTS-OF-TERM2))
 (438 2 (:REWRITE PSEUDO-TERM-LISTP-OF-GET-CONJUNCTS-OF-TERM2))
 (405 405 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (369 369 (:REWRITE DEFAULT-<-1))
 (369 369 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (257 257 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (228 76 (:REWRITE +-COMBINE-CONSTANTS))
 (222 1 (:REWRITE DISJUNCT-LISTP-OF-NEGATE-CONJUNCTS))
 (222 1 (:REWRITE CONJUNCT-LISTP-OF-NEGATE-DISJUNCTS))
 (148 74 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (146 112 (:DEFINITION FIX))
 (144 144 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (124 4 (:DEFINITION PSEUDO-TERM-LISTP))
 (88 44 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (81 81 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (80 40 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (80 40 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (80 40 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (76 76 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (72 72 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (68 68 (:REWRITE EQUAL-OF-LEN-AND-0))
 (44 44 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (36 36 (:REWRITE DEFAULT-COERCE-2))
 (36 36 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:TYPE-PRESCRIPTION GET-DISJUNCTS-OF-TERM2))
 (8 8 (:TYPE-PRESCRIPTION GET-CONJUNCTS-OF-TERM2))
 )
(FLAG-LEMMA-FOR-LOGIC-TERM-LISTP-OF-GET-CONJUNCTS-OF-TERM2
 (51421 4696 (:REWRITE DEFAULT-CDR))
 (9713 1100 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (6243 6243 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4718 2711 (:REWRITE DEFAULT-+-2))
 (3332 1772 (:REWRITE DEFAULT-<-2))
 (2711 2711 (:REWRITE DEFAULT-+-1))
 (1839 507 (:REWRITE +-COMBINE-CONSTANTS))
 (1789 1789 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1772 1772 (:REWRITE DEFAULT-<-1))
 (1624 1624 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (1395 1395 (:REWRITE EQUAL-OF-LEN-AND-0))
 (542 76 (:REWRITE LOGIC-TERMP-WHEN-QUOTEP))
 (411 55 (:DEFINITION QUOTEP))
 (390 390 (:REWRITE ARITIES-OKP-IMPLIES-ARITY))
 (336 84 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (55 55 (:TYPE-PRESCRIPTION QUOTEP))
 (42 42 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 )
(LOGIC-TERM-LISTP-OF-GET-CONJUNCTS-OF-TERM2)
(LOGIC-TERM-LISTP-OF-GET-DISJUNCTS-OF-TERM2)
(GET-CONJUNCTS-OF-TERMS2)