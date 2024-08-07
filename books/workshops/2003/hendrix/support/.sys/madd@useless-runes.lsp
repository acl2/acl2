(M+
 (112 2 (:DEFINITION ACL2-COUNT))
 (75 6 (:REWRITE ROW-CDR-EMPTY))
 (50 20 (:REWRITE DEFAULT-+-2))
 (37 3 (:DEFINITION ROW-COUNT-DEF))
 (32 19 (:TYPE-PRESCRIPTION ROW-COUNT-TYPE-NOT-EMPTY))
 (32 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (26 20 (:REWRITE DEFAULT-+-1))
 (20 4 (:DEFINITION INTEGER-ABS))
 (19 19 (:TYPE-PRESCRIPTION ROW-COUNT-TYPE))
 (18 2 (:DEFINITION LENGTH))
 (16 4 (:REWRITE COMMUTATIVITY-OF-+))
 (12 2 (:DEFINITION LEN))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:TYPE-PRESCRIPTION CONSP-ROW-CAR))
 (4 1 (:DEFINITION FIX))
 (2 2 (:TYPE-PRESCRIPTION LEN-CONSP))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (2 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (1 1 (:TYPE-PRESCRIPTION MATRIXP))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 )
(M-EMPTYP-M+
 (876 3 (:DEFINITION V+))
 (503 11 (:REWRITE DEFAULT-+-2))
 (468 72 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (450 12 (:REWRITE CAR-VECTOR-TYPE))
 (393 159 (:TYPE-PRESCRIPTION CONSP-ROW-CAR))
 (354 6 (:DEFINITION MVECTORP))
 (311 11 (:REWRITE DEFAULT-+-1))
 (270 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (192 96 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (185 14 (:REWRITE ROW-CDR-EMPTY))
 (108 108 (:TYPE-PRESCRIPTION MVECTORP))
 (80 51 (:TYPE-PRESCRIPTION ROW-COUNT-TYPE-NOT-EMPTY))
 (75 7 (:DEFINITION ROW-COUNT-DEF))
 (51 51 (:TYPE-PRESCRIPTION ROW-COUNT-TYPE))
 (51 12 (:REWRITE DEFAULT-CAR))
 (39 12 (:REWRITE DEFAULT-CDR))
 (39 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (30 12 (:REWRITE CONSP-ROW-CAR))
 (18 6 (:REWRITE MVECTORP-ROW-CAR))
 (18 6 (:DEFINITION ROW-CAR-DEF))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 1 (:DEFINITION FIX))
 (2 1 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 )
(ROW-COUNT-M+
 (876 3 (:DEFINITION V+))
 (567 27 (:REWRITE DEFAULT-+-2))
 (468 72 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (450 12 (:REWRITE CAR-VECTOR-TYPE))
 (434 30 (:REWRITE ROW-CDR-EMPTY))
 (393 159 (:TYPE-PRESCRIPTION CONSP-ROW-CAR))
 (354 6 (:DEFINITION MVECTORP))
 (327 27 (:REWRITE DEFAULT-+-1))
 (270 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (192 96 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (108 108 (:TYPE-PRESCRIPTION MVECTORP))
 (75 19 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (51 12 (:REWRITE DEFAULT-CAR))
 (39 12 (:REWRITE DEFAULT-CDR))
 (30 12 (:REWRITE CONSP-ROW-CAR))
 (19 19 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 6 (:REWRITE MVECTORP-ROW-CAR))
 (18 6 (:DEFINITION ROW-CAR-DEF))
 (8 2 (:DEFINITION FIX))
 (4 2 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (3 3 (:REWRITE M-EMPTYP-M+))
 )
(COL-COUNT-M+
 (387 19 (:REWRITE DEFAULT-+-2))
 (386 2 (:DEFINITION V+))
 (208 84 (:TYPE-PRESCRIPTION CONSP-ROW-CAR))
 (194 26 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (166 4 (:REWRITE CAR-VECTOR-TYPE))
 (136 9 (:DEFINITION COL-COUNT-DEF))
 (130 2 (:DEFINITION MVECTORP))
 (125 9 (:REWRITE COL-CDR-EMPTY))
 (112 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (73 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (66 34 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (64 4 (:DEFINITION ROW-CAR-DEF))
 (40 8 (:REWRITE DEFAULT-CAR))
 (38 38 (:TYPE-PRESCRIPTION MVECTORP))
 (29 19 (:REWRITE DEFAULT-+-1))
 (26 6 (:REWRITE DEFAULT-CDR))
 (14 6 (:REWRITE CONSP-ROW-CAR))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 2 (:DEFINITION FIX))
 (7 7 (:TYPE-PRESCRIPTION COL-CDR))
 (6 2 (:REWRITE MVECTORP-ROW-CAR))
 (4 2 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (3 1 (:REWRITE COL-COUNT-IMPLIES-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (2 2 (:TYPE-PRESCRIPTION COL-CAR))
 )
(MATRIXP-M+
 (579 3 (:DEFINITION V+))
 (512 12 (:REWRITE DEFAULT-+-2))
 (291 39 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (249 6 (:REWRITE CAR-VECTOR-TYPE))
 (195 3 (:DEFINITION MVECTORP))
 (168 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (110 8 (:REWRITE ROW-CDR-EMPTY))
 (105 8 (:REWRITE COL-CDR-EMPTY))
 (99 51 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (96 6 (:DEFINITION ROW-CAR-DEF))
 (74 5 (:DEFINITION COL-COUNT-DEF))
 (60 12 (:REWRITE DEFAULT-CAR))
 (39 9 (:REWRITE DEFAULT-CDR))
 (38 4 (:DEFINITION ROW-COUNT-DEF))
 (27 12 (:REWRITE DEFAULT-+-1))
 (21 9 (:REWRITE CONSP-ROW-CAR))
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (9 3 (:REWRITE MVECTORP-ROW-CAR))
 (5 5 (:TYPE-PRESCRIPTION COL-CDR))
 (3 3 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (3 3 (:TYPE-PRESCRIPTION COL-CAR))
 )
(M+
 (440 96 (:REWRITE DEFAULT-+-2))
 (319 75 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (289 1 (:DEFINITION M+))
 (288 20 (:REWRITE COL-CDR-EMPTY))
 (136 1 (:DEFINITION V+))
 (134 96 (:REWRITE DEFAULT-+-1))
 (97 2 (:DEFINITION ROW-CAR-DEF))
 (75 75 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (42 2 (:REWRITE CAR-VECTOR-TYPE))
 (40 4 (:REWRITE DEFAULT-CAR))
 (36 4 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (27 7 (:REWRITE CONSP-ROW-CAR))
 (20 2 (:REWRITE DEFAULT-CDR))
 (18 18 (:TYPE-PRESCRIPTION COL-CDR))
 (16 8 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (12 6 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (8 4 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (6 6 (:TYPE-PRESCRIPTION MVECTORP))
 (6 2 (:REWRITE MVECTORP-ROW-CAR))
 (6 2 (:REWRITE CONSP-COL-CAR))
 (4 4 (:TYPE-PRESCRIPTION COL-CAR))
 (4 4 (:REWRITE EQUAL-CONSTANT-+))
 )
(COL-CAR-M+
 (1710 137 (:REWRITE ROW-CDR-EMPTY))
 (799 65 (:DEFINITION ROW-COUNT-DEF))
 (698 20 (:DEFINITION ROW-CAR-DEF))
 (600 42 (:REWRITE COL-CDR-EMPTY))
 (481 78 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (466 81 (:REWRITE DEFAULT-CAR))
 (375 19 (:REWRITE CAR-VECTOR-TYPE))
 (304 22 (:DEFINITION COL-COUNT-DEF))
 (293 113 (:REWRITE DEFAULT-+-1))
 (239 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (183 5 (:DEFINITION MVECTORP))
 (133 28 (:REWRITE DEFAULT-CDR))
 (132 6 (:REWRITE ROW-COUNT-M+))
 (121 31 (:REWRITE CONSP-ROW-CAR))
 (78 78 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (34 14 (:REWRITE CONSP-COL-CAR))
 (26 13 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (22 22 (:TYPE-PRESCRIPTION COL-CDR))
 (15 5 (:REWRITE MVECTORP-ROW-CAR))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(M+-BY-COL-RECURSION
 (613 132 (:REWRITE DEFAULT-+-2))
 (166 12 (:REWRITE ROW-CDR-EMPTY))
 (136 132 (:REWRITE DEFAULT-+-1))
 (74 74 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (70 2 (:DEFINITION ACL2-COUNT))
 (10 2 (:DEFINITION INTEGER-ABS))
 (9 1 (:DEFINITION LENGTH))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 1 (:DEFINITION LEN))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION LEN-CONSP))
 (1 1 (:TYPE-PRESCRIPTION LEN))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(M+-BY-COL-DEF
 (14475 1050 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7736 791 (:REWRITE DEFAULT-CAR))
 (4749 2115 (:REWRITE DEFAULT-+-1))
 (2077 347 (:REWRITE DEFAULT-CDR))
 (1732 70 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1050 1050 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (772 193 (:REWRITE COL-COUNT-IMPLIES-EMPTY))
 (662 20 (:REWRITE EMPTY-ROW-CDR-COL-CDR))
 (336 6 (:REWRITE ROW-COUNT-ROW-CDR-COL-CDR))
 (212 4 (:REWRITE V+-COMM))
 (206 103 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (40 20 (:DEFINITION CASE-SPLIT))
 (18 2 (:REWRITE CONS-CAR-CDR))
 )
(M+-ASSOC
 (17861 110 (:DEFINITION V+))
 (11027 1076 (:REWRITE DEFAULT-+-2))
 (8722 120 (:DEFINITION COL-CAR-DEF))
 (6735 420 (:REWRITE COL-CDR-EMPTY))
 (4084 130 (:DEFINITION ROW-CAR-DEF))
 (3854 625 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3340 198 (:REWRITE CAR-VECTOR-TYPE))
 (3081 552 (:REWRITE DEFAULT-CAR))
 (2948 1076 (:REWRITE DEFAULT-+-1))
 (2919 14 (:REWRITE COL-CAR-M+))
 (2767 16 (:REWRITE V+-COMM))
 (2572 1335 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (2116 109 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1756 45 (:REWRITE COL-COUNT-M+))
 (1455 260 (:REWRITE DEFAULT-CDR))
 (1422 6 (:REWRITE COL-CDR-ROW-CONS))
 (1335 1335 (:TYPE-PRESCRIPTION COL-CAR))
 (1176 6 (:DEFINITION LEN))
 (840 12 (:REWRITE MATRIXP-ROW-CONS))
 (797 35 (:REWRITE LEN-V+))
 (738 18 (:DEFINITION MVECTORP))
 (715 29 (:REWRITE LEN-COL-CAR))
 (695 10 (:REWRITE COMMUTATIVITY-OF-+))
 (674 337 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (657 211 (:REWRITE CONSP-ROW-CAR))
 (625 625 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (615 615 (:TYPE-PRESCRIPTION V+))
 (565 157 (:REWRITE CONSP-V+))
 (534 214 (:REWRITE CONSP-COL-CAR))
 (481 320 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (250 250 (:TYPE-PRESCRIPTION COL-CDR))
 (240 80 (:REWRITE MATRIXP-M+))
 (198 66 (:REWRITE MVECTORP-COL-CAR))
 (179 8 (:REWRITE ROW-COUNT-M+))
 (126 72 (:REWRITE M-EMPTYP-M+))
 (89 21 (:REWRITE MVECTORP-ROW-CAR))
 (65 65 (:REWRITE MVECTORP-V+))
 (32 8 (:REWRITE DEFAULT-<-1))
 (27 8 (:REWRITE DEFAULT-<-2))
 (21 21 (:REWRITE CDR-CONS))
 (18 18 (:REWRITE CAR-CONS))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 6 (:REWRITE EQUAL-CONSTANT-+))
 )
(M+-ASSOC2
 (19385 122 (:DEFINITION V+))
 (12480 1146 (:REWRITE DEFAULT-+-2))
 (9598 126 (:DEFINITION COL-CAR-DEF))
 (7879 464 (:REWRITE COL-CDR-EMPTY))
 (4843 148 (:DEFINITION ROW-CAR-DEF))
 (4254 666 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3528 208 (:REWRITE CAR-VECTOR-TYPE))
 (3510 600 (:REWRITE DEFAULT-CAR))
 (2966 1146 (:REWRITE DEFAULT-+-1))
 (2744 14 (:REWRITE COL-CAR-M+))
 (2730 120 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2552 1328 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (1973 40 (:REWRITE COL-COUNT-M+))
 (1642 278 (:REWRITE DEFAULT-CDR))
 (1422 6 (:REWRITE COL-CDR-ROW-CONS))
 (1328 1328 (:TYPE-PRESCRIPTION COL-CAR))
 (840 12 (:REWRITE MATRIXP-ROW-CONS))
 (738 18 (:DEFINITION MVECTORP))
 (702 290 (:REWRITE CONSP-ROW-CAR))
 (666 666 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (640 320 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (624 428 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (588 236 (:REWRITE CONSP-COL-CAR))
 (586 586 (:TYPE-PRESCRIPTION V+))
 (568 144 (:REWRITE CONSP-V+))
 (528 24 (:REWRITE LEN-V+))
 (297 12 (:REWRITE LEN-COL-CAR))
 (264 264 (:TYPE-PRESCRIPTION COL-CDR))
 (216 72 (:REWRITE MVECTORP-COL-CAR))
 (184 8 (:REWRITE ROW-COUNT-M+))
 (150 50 (:REWRITE MATRIXP-M+))
 (100 28 (:REWRITE MVECTORP-ROW-CAR))
 (76 42 (:REWRITE M-EMPTYP-M+))
 (60 60 (:REWRITE MVECTORP-V+))
 (18 18 (:REWRITE CDR-CONS))
 (18 18 (:REWRITE CAR-CONS))
 (6 6 (:REWRITE NOT-EMPTY-ROW-CONS))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 )
(M+-COMM
 (4229 30 (:DEFINITION V+))
 (3261 42 (:DEFINITION COL-CAR-DEF))
 (3211 525 (:REWRITE DEFAULT-+-2))
 (2440 172 (:REWRITE COL-CDR-EMPTY))
 (2433 275 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1586 54 (:DEFINITION ROW-CAR-DEF))
 (1102 525 (:REWRITE DEFAULT-+-1))
 (827 184 (:REWRITE DEFAULT-CAR))
 (630 339 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (549 36 (:REWRITE CAR-VECTOR-TYPE))
 (405 6 (:REWRITE COMMUTATIVITY-OF-+))
 (339 339 (:TYPE-PRESCRIPTION COL-CAR))
 (311 70 (:REWRITE DEFAULT-CDR))
 (297 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (297 12 (:REWRITE LEN-COL-CAR))
 (275 275 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (234 6 (:DEFINITION LEN))
 (216 108 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (150 54 (:REWRITE CONSP-ROW-CAR))
 (144 96 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (126 54 (:REWRITE CONSP-COL-CAR))
 (100 100 (:TYPE-PRESCRIPTION COL-CDR))
 (63 21 (:REWRITE MVECTORP-COL-CAR))
 (27 9 (:REWRITE MVECTORP-ROW-CAR))
 (18 18 (:REWRITE CDR-CONS))
 (12 12 (:REWRITE CAR-CONS))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 )
(M+ZERO
 (2174 3 (:DEFINITION M+-BY-COL-DEF))
 (1344 6 (:DEFINITION V+))
 (909 139 (:REWRITE DEFAULT-+-2))
 (863 10 (:DEFINITION COL-CAR-DEF))
 (581 37 (:REWRITE COL-CDR-EMPTY))
 (530 76 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (405 23 (:DEFINITION VZERO))
 (388 22 (:DEFINITION COL-COUNT-DEF))
 (327 37 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (320 139 (:REWRITE DEFAULT-+-1))
 (319 37 (:REWRITE DEFAULT-CAR))
 (316 9 (:DEFINITION ROW-CAR-DEF))
 (277 104 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (275 1 (:REWRITE V+-COMM))
 (269 5 (:REWRITE COL-CONS-ROW-CONS-UNIT))
 (262 12 (:REWRITE CAR-VECTOR-TYPE))
 (212 30 (:REWRITE M-EMPTY-ZERO))
 (174 17 (:REWRITE ZP-OPEN))
 (123 16 (:REWRITE DEFAULT-CDR))
 (120 19 (:REWRITE CONSP-COL-CAR))
 (119 1 (:REWRITE COL-CDR-ROW-CONS))
 (114 2 (:REWRITE MATRIXP-ROW-CONS))
 (104 104 (:TYPE-PRESCRIPTION COL-CAR))
 (103 17 (:REWRITE CONSP-ROW-CAR))
 (102 9 (:REWRITE LEN-VZERO))
 (93 9 (:DEFINITION NFIX))
 (76 76 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (76 1 (:REWRITE V+-NIL))
 (65 1 (:REWRITE COMMUTATIVITY-OF-+))
 (61 1 (:DEFINITION MVECTORP))
 (60 22 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (52 52 (:TYPE-PRESCRIPTION VZERO))
 (51 17 (:REWRITE ROW-COUNT-IMPLIES-NOT-EMPTY))
 (51 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (48 8 (:REWRITE COL-COUNT-ZERO))
 (28 9 (:REWRITE DEFAULT-<-1))
 (27 9 (:REWRITE CONSP-VZERO))
 (27 2 (:DEFINITION LEN))
 (26 13 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (22 22 (:TYPE-PRESCRIPTION COL-CDR))
 (18 6 (:REWRITE MVECTORP-COL-CAR))
 (9 9 (:TYPE-PRESCRIPTION MVECTORP-VZERO))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
 (9 3 (:REWRITE MVECTORP-ROW-CAR))
 (6 1 (:REWRITE LEN-COL-CAR))
 (5 5 (:REWRITE CDR-CONS))
 (3 3 (:REWRITE CAR-CONS))
 (1 1 (:REWRITE NOT-EMPTY-ROW-CONS))
 )
(ZERO+M
 (2335 3 (:DEFINITION M+-BY-COL-DEF))
 (1435 6 (:DEFINITION V+))
 (1019 5 (:REWRITE V+-COMM))
 (983 157 (:REWRITE DEFAULT-+-2))
 (716 95 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (641 10 (:DEFINITION COL-CAR-DEF))
 (611 39 (:REWRITE COL-CDR-EMPTY))
 (432 24 (:DEFINITION COL-COUNT-DEF))
 (405 23 (:DEFINITION VZERO))
 (394 157 (:REWRITE DEFAULT-+-1))
 (377 45 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (316 126 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (316 9 (:DEFINITION ROW-CAR-DEF))
 (297 37 (:REWRITE DEFAULT-CAR))
 (280 15 (:REWRITE CAR-VECTOR-TYPE))
 (269 5 (:REWRITE COL-CONS-ROW-CONS-UNIT))
 (268 33 (:REWRITE M-EMPTY-ZERO))
 (245 24 (:REWRITE ZP-OPEN))
 (171 3 (:REWRITE MATRIXP-ROW-CONS))
 (156 3 (:REWRITE COMMUTATIVITY-OF-+))
 (129 18 (:REWRITE DEFAULT-CDR))
 (128 7 (:REWRITE LEN-COL-CAR))
 (126 126 (:TYPE-PRESCRIPTION COL-CAR))
 (120 19 (:REWRITE CONSP-COL-CAR))
 (119 1 (:REWRITE COL-CDR-ROW-CONS))
 (113 10 (:REWRITE LEN-VZERO))
 (103 17 (:REWRITE CONSP-ROW-CAR))
 (103 10 (:DEFINITION NFIX))
 (102 4 (:DEFINITION LEN))
 (95 95 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (76 1 (:REWRITE V+-NIL))
 (72 24 (:REWRITE ROW-COUNT-IMPLIES-NOT-EMPTY))
 (71 28 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (66 66 (:TYPE-PRESCRIPTION VZERO))
 (61 1 (:DEFINITION MVECTORP))
 (44 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (33 11 (:REWRITE CONSP-VZERO))
 (31 10 (:REWRITE DEFAULT-<-1))
 (24 24 (:TYPE-PRESCRIPTION COL-CDR))
 (21 7 (:REWRITE MVECTORP-COL-CAR))
 (20 10 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (13 13 (:TYPE-PRESCRIPTION MVECTORP-VZERO))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (9 3 (:REWRITE MVECTORP-ROW-CAR))
 (7 7 (:REWRITE CDR-CONS))
 (3 3 (:REWRITE CAR-CONS))
 )
(ROW-M+
 (8020 117 (:DEFINITION COL-CAR-DEF))
 (7585 991 (:REWRITE DEFAULT-+-2))
 (6053 384 (:REWRITE COL-CDR-EMPTY))
 (4276 67 (:REWRITE NTH-OVER))
 (4041 115 (:DEFINITION ROW-CAR-DEF))
 (3380 213 (:DEFINITION COL-COUNT-DEF))
 (2690 511 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (2631 1977 (:TYPE-PRESCRIPTION COL-COUNT-TYPE-NOT-EMPTY))
 (2494 428 (:REWRITE DEFAULT-CAR))
 (2148 598 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2022 1048 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (1977 1977 (:TYPE-PRESCRIPTION COL-COUNT-TYPE))
 (1970 93 (:REWRITE CAR-VECTOR-TYPE))
 (1932 41 (:DEFINITION NTH))
 (1864 29 (:DEFINITION LEN))
 (1715 75 (:REWRITE COL-COUNT-ROW-CDR))
 (1635 991 (:REWRITE DEFAULT-+-1))
 (1427 110 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1240 41 (:REWRITE COL-COUNT-M+))
 (1116 6 (:REWRITE COL-CDR-ROW-CONS))
 (1110 54 (:REWRITE LEN-COL-CAR))
 (965 171 (:REWRITE DEFAULT-CDR))
 (888 12 (:REWRITE MATRIXP-ROW-CONS))
 (884 23 (:DEFINITION MVECTORP))
 (813 3 (:REWRITE NTH-V+))
 (775 35 (:REWRITE LEN-V+))
 (598 598 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (552 24 (:REWRITE LEN-ROW-CAR))
 (522 146 (:TYPE-PRESCRIPTION LEN-CONSP))
 (424 424 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (417 143 (:REWRITE CONSP-COL-CAR))
 (402 238 (:REWRITE DEFAULT-<-2))
 (345 345 (:META CANCEL_PLUS-LESSP-CORRECT))
 (326 163 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (326 126 (:REWRITE CONSP-ROW-CAR))
 (312 238 (:REWRITE DEFAULT-<-1))
 (213 213 (:TYPE-PRESCRIPTION COL-CDR))
 (200 50 (:DEFINITION FIX))
 (160 6 (:REWRITE M+-COMM))
 (146 146 (:TYPE-PRESCRIPTION LEN))
 (72 36 (:REWRITE CONSP-V+))
 (57 19 (:REWRITE FOLD-CONSTS-IN-+))
 (36 36 (:REWRITE CDR-CONS))
 (18 18 (:REWRITE MVECTORP-V+))
 (18 18 (:REWRITE CAR-CONS))
 )
(COL-M+
 (11222 728 (:REWRITE COL-CDR-EMPTY))
 (9021 490 (:DEFINITION COL-COUNT-DEF))
 (6896 184 (:DEFINITION ROW-CAR-DEF))
 (6706 139 (:DEFINITION COL-CAR-DEF))
 (4360 652 (:REWRITE DEFAULT-CAR))
 (3881 143 (:REWRITE CAR-VECTOR-TYPE))
 (3146 1716 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (2827 1589 (:REWRITE DEFAULT-+-1))
 (2245 49 (:DEFINITION MVECTORP))
 (1989 149 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1765 287 (:REWRITE DEFAULT-CDR))
 (1142 314 (:REWRITE CONSP-ROW-CAR))
 (1038 450 (:REWRITE DEFAULT-<-2))
 (974 974 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (586 62 (:DEFINITION LEN))
 (517 450 (:REWRITE DEFAULT-<-1))
 (510 510 (:META CANCEL_PLUS-LESSP-CORRECT))
 (490 490 (:TYPE-PRESCRIPTION COL-CDR))
 (483 149 (:REWRITE CONSP-COL-CAR))
 (352 16 (:REWRITE ROW-COUNT-M+))
 (304 8 (:REWRITE M+-COMM))
 (268 134 (:REWRITE ROW-COUNT-IMPLIES-EMPTY))
 (240 240 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (240 60 (:REWRITE <-+-NEGATIVE-0-1))
 (150 2 (:REWRITE V+-COMM))
 (86 86 (:REWRITE ZP-OPEN))
 (58 29 (:TYPE-PRESCRIPTION MVECTORP-COL))
 (48 16 (:REWRITE MVECTORP-ROW-CAR))
 )
(ENTRY-M+
 (6416 46 (:DEFINITION ROW-BY-COL-DEF))
 (3538 329 (:REWRITE ROW-CDR-EMPTY))
 (3374 536 (:REWRITE DEFAULT-+-2))
 (3077 246 (:REWRITE COL-CDR-EMPTY))
 (2308 15 (:DEFINITION V+))
 (2105 150 (:DEFINITION COL-COUNT-DEF))
 (1349 48 (:DEFINITION ROW-CAR-DEF))
 (1189 48 (:DEFINITION COL-CAR-DEF))
 (1182 219 (:REWRITE DEFAULT-CAR))
 (922 46 (:REWRITE LEN-COL-CAR))
 (843 206 (:TYPE-PRESCRIPTION CAR-VECTOR-TYPE))
 (826 428 (:REWRITE DEFAULT-<-2))
 (806 536 (:REWRITE DEFAULT-+-1))
 (792 30 (:REWRITE CAR-VECTOR-TYPE))
 (686 111 (:REWRITE DEFAULT-CDR))
 (487 47 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (471 428 (:REWRITE DEFAULT-<-1))
 (461 461 (:META CANCEL_PLUS-LESSP-CORRECT))
 (422 406 (:TYPE-PRESCRIPTION CONSP-COL-CAR))
 (412 412 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (412 412 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (406 406 (:TYPE-PRESCRIPTION COL-CAR))
 (364 40 (:DEFINITION LEN))
 (328 8 (:DEFINITION MVECTORP))
 (268 268 (:TYPE-PRESCRIPTION MVECTORP))
 (225 1 (:DEFINITION M+))
 (207 1 (:DEFINITION M+-BY-COL-DEF))
 (150 150 (:TYPE-PRESCRIPTION COL-CDR))
 (132 132 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (132 33 (:REWRITE <-+-NEGATIVE-0-1))
 (68 68 (:TYPE-PRESCRIPTION MVECTORP-ROW))
 (51 51 (:REWRITE ZP-OPEN))
 (24 24 (:TYPE-PRESCRIPTION MVECTORP-ROW-CAR))
 (8 8 (:TYPE-PRESCRIPTION MVECTORP-COL-CAR))
 (5 3 (:REWRITE CONSP-ROW-CAR))
 (5 3 (:REWRITE CONSP-COL-CAR))
 )
