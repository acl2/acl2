(MOD-+-DISTRIBUTE-1
 (241 32 (:REWRITE COMMUTATIVITY-OF-*))
 (187 20 (:REWRITE CANCEL-MOD-+-BASIC))
 (182 11 (:REWRITE MOD-=-0 . 2))
 (182 4 (:LINEAR MOD-TYPE . 2))
 (133 13 (:REWRITE DISTRIBUTIVITY))
 (127 127 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (127 127 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (127 127 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (119 95 (:REWRITE DEFAULT-*-2))
 (107 95 (:REWRITE DEFAULT-*-1))
 (87 74 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (46 28 (:REWRITE DEFAULT-+-2))
 (46 28 (:REWRITE DEFAULT-+-1))
 (45 45 (:REWRITE INTEGERP-+-MINUS-*))
 (41 41 (:REWRITE DEFAULT-<-2))
 (41 41 (:REWRITE DEFAULT-<-1))
 (37 37 (:REWRITE DEFAULT-UNARY-/))
 (31 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (31 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (31 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (31 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (13 13 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (13 13 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (11 11 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (4 4 (:LINEAR MOD-TYPE . 3))
 (4 4 (:LINEAR MOD-TYPE . 1))
 )
(MOD-+-DISTRIBUTE-2
 (223 32 (:REWRITE COMMUTATIVITY-OF-*))
 (187 20 (:REWRITE CANCEL-MOD-+-BASIC))
 (182 11 (:REWRITE MOD-=-0 . 2))
 (164 4 (:LINEAR MOD-TYPE . 2))
 (129 129 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (129 129 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (129 129 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (119 95 (:REWRITE DEFAULT-*-2))
 (115 13 (:REWRITE DISTRIBUTIVITY))
 (107 95 (:REWRITE DEFAULT-*-1))
 (87 74 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (45 45 (:REWRITE INTEGERP-+-MINUS-*))
 (45 15 (:REWRITE MOD-+-DISTRIBUTE-1))
 (41 41 (:REWRITE DEFAULT-<-2))
 (41 41 (:REWRITE DEFAULT-<-1))
 (38 20 (:REWRITE DEFAULT-+-2))
 (37 37 (:REWRITE DEFAULT-UNARY-/))
 (31 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (31 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (31 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (31 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (20 20 (:REWRITE DEFAULT-+-1))
 (13 13 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (13 13 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (11 11 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (4 4 (:LINEAR MOD-TYPE . 3))
 (4 4 (:LINEAR MOD-TYPE . 1))
 )
(MOD-+-DISTRIBUTE-3
 (784 40 (:REWRITE MOD-=-0 . 2))
 (764 84 (:REWRITE COMMUTATIVITY-OF-*))
 (544 40 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (544 40 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (544 40 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (544 40 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (428 32 (:REWRITE DISTRIBUTIVITY))
 (412 232 (:REWRITE DEFAULT-*-2))
 (400 16 (:REWRITE CANCEL-MOD-+-BASIC))
 (396 20 (:LINEAR MOD-TYPE . 2))
 (349 349 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (349 349 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (349 349 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (316 232 (:REWRITE DEFAULT-*-1))
 (228 168 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (208 160 (:REWRITE DEFAULT-<-2))
 (208 160 (:REWRITE DEFAULT-<-1))
 (208 8 (:REWRITE CANCEL-MOD-+-3))
 (128 32 (:REWRITE DEFAULT-+-2))
 (104 104 (:REWRITE INTEGERP-+-MINUS-*))
 (84 84 (:REWRITE DEFAULT-UNARY-/))
 (60 60 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (40 40 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (32 32 (:REWRITE DEFAULT-+-1))
 (32 8 (:REWRITE MOD-+-DISTRIBUTE-2))
 (32 8 (:REWRITE MOD-+-DISTRIBUTE-1))
 (20 20 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (20 20 (:LINEAR MOD-TYPE . 3))
 (20 20 (:LINEAR MOD-TYPE . 1))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 )
(LOGCONS-X-TO-0)
(LOGHEAD-16-WORD-P
 (4 2 (:LINEAR LOGHEAD-UPPER-BOUND))
 (4 2 (:LINEAR LOGHEAD-LEQ))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 )
(LOGBITP-0
 (6 2 (:REWRITE LOGCAR-BITP))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:DEFINITION BITP))
 )
(LOGHEAD-INDUCTION
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(LOGHEAD**
 (3852 40 (:REWRITE LOGHEAD-IDENTITY))
 (3494 119 (:DEFINITION UNSIGNED-BYTE-P))
 (3030 79 (:DEFINITION INTEGER-RANGE-P))
 (2748 38 (:REWRITE LOGCAR-BITP))
 (2654 28 (:DEFINITION BITP))
 (1764 80 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (530 224 (:REWRITE DEFAULT-<-2))
 (370 306 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (370 150 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (340 104 (:REWRITE LOGCDR-<-0))
 (293 224 (:REWRITE DEFAULT-<-1))
 (121 89 (:REWRITE DEFAULT-+-2))
 (119 119 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (119 119 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (118 118 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
 (89 89 (:REWRITE DEFAULT-+-1))
 (67 13 (:LINEAR LOGHEAD-LEQ))
 (64 64 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (58 58 (:TYPE-PRESCRIPTION BITP))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(UNSIGNED-BYTE-P-LOGCONS
 (27 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (3 1 (:LINEAR EXPT->-1))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 )
(UNSIGNED-BYTE-P-<
 (20 10 (:REWRITE DEFAULT-<-2))
 (14 10 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (3 1 (:LINEAR EXPT->-1))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
 (1 1 (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
 (1 1 (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE<1))
 )
(UNSIGNED-BYTE-P-+
 (43 2 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (25 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-<))
 (7 1 (:REWRITE BIT-P-UNSIGNED-BYTE-P-1))
 (6 1 (:REWRITE PLUS-UNSIGNED-BYTE-P-LT-2-*-EXPT-2-WIDTH))
 (6 1 (:REWRITE PLUS-UNSIGNED-BYTE-LT-EXPT-2-WIDTH-IF-LOGBIT))
 (5 1 (:DEFINITION BITP))
 (4 1 (:REWRITE DEFAULT-*-2))
 (4 1 (:LINEAR EXPT->-1))
 (3 1 (:REWRITE NORMALIZE-EQUAL-0))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:DEFINITION FIX))
 )
(WORD-ADD-WORD-1
 (120 11 (:REWRITE MOD-=-0 . 2))
 (71 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (71 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (71 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (71 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (67 16 (:REWRITE COMMUTATIVITY-OF-*))
 (65 65 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (65 65 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (65 65 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (56 40 (:REWRITE DEFAULT-<-2))
 (56 40 (:REWRITE DEFAULT-<-1))
 (48 4 (:LINEAR MOD-TYPE . 2))
 (46 34 (:REWRITE DEFAULT-*-2))
 (46 34 (:REWRITE DEFAULT-*-1))
 (17 17 (:REWRITE INTEGERP-+-MINUS-*))
 (16 4 (:REWRITE CANCEL-MOD-+-BASIC))
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 6 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (9 3 (:REWRITE MOD-+-DISTRIBUTE-2))
 (9 3 (:REWRITE MOD-+-DISTRIBUTE-1))
 (7 1 (:REWRITE DISTRIBUTIVITY))
 (4 4 (:LINEAR MOD-TYPE . 3))
 (4 4 (:LINEAR MOD-TYPE . 1))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(WORD-ADD-WORD-2
 (120 11 (:REWRITE MOD-=-0 . 2))
 (71 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (71 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (71 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (71 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (67 16 (:REWRITE COMMUTATIVITY-OF-*))
 (62 62 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (62 62 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (62 62 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (56 40 (:REWRITE DEFAULT-<-2))
 (56 40 (:REWRITE DEFAULT-<-1))
 (48 4 (:LINEAR MOD-TYPE . 2))
 (46 34 (:REWRITE DEFAULT-*-2))
 (46 34 (:REWRITE DEFAULT-*-1))
 (17 17 (:REWRITE INTEGERP-+-MINUS-*))
 (16 4 (:REWRITE CANCEL-MOD-+-BASIC))
 (11 11 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (10 4 (:REWRITE DEFAULT-+-2))
 (9 3 (:REWRITE MOD-+-DISTRIBUTE-2))
 (9 3 (:REWRITE MOD-+-DISTRIBUTE-1))
 (7 1 (:REWRITE DISTRIBUTIVITY))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR MOD-TYPE . 3))
 (4 4 (:LINEAR MOD-TYPE . 1))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(EXPR-ENFORCED-WORD-P)
(EXPR-ADDITION-WITH-WORD-IN-IT-P
 (2392 214 (:REWRITE MEM-ALIST-P-CAR))
 (2178 83 (:DEFINITION MEM-ALIST-P))
 (1632 701 (:REWRITE DEFAULT-+-2))
 (1083 104 (:REWRITE MEM-ALIST-P-CDR))
 (1003 701 (:REWRITE DEFAULT-+-1))
 (608 152 (:DEFINITION INTEGER-ABS))
 (468 468 (:TYPE-PRESCRIPTION MEM-ALIST-P))
 (421 421 (:REWRITE MEM-ALIST-P-MEMBERP-EQUAL))
 (421 421 (:REWRITE MEM-ALIST-P-MEMBER-EQUAL))
 (233 180 (:REWRITE DEFAULT-<-2))
 (203 180 (:REWRITE DEFAULT-<-1))
 (189 189 (:TYPE-PRESCRIPTION ADDR-P))
 (152 152 (:REWRITE DEFAULT-UNARY-MINUS))
 (129 129 (:REWRITE MEM-ALIST-P-INITIAL-SUBLISTP-EQUAL))
 (126 126 (:TYPE-PRESCRIPTION WORD-P))
 (76 76 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (76 76 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (76 76 (:REWRITE DEFAULT-REALPART))
 (76 76 (:REWRITE DEFAULT-NUMERATOR))
 (76 76 (:REWRITE DEFAULT-IMAGPART))
 (76 76 (:REWRITE DEFAULT-DENOMINATOR))
 (63 63 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (63 63 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (32 16 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(FERMENT-WORD-TO-ADD
 (120 11 (:REWRITE MOD-=-0 . 2))
 (71 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (71 11 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (71 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (71 11 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (67 16 (:REWRITE COMMUTATIVITY-OF-*))
 (62 62 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (62 62 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (62 62 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (56 40 (:REWRITE DEFAULT-<-2))
 (56 40 (:REWRITE DEFAULT-<-1))
 (48 4 (:LINEAR MOD-TYPE . 2))
 (46 34 (:REWRITE DEFAULT-*-2))
 (46 34 (:REWRITE DEFAULT-*-1))
 (17 17 (:REWRITE INTEGERP-+-MINUS-*))
 (16 4 (:REWRITE CANCEL-MOD-+-BASIC))
 (11 11 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (10 4 (:REWRITE DEFAULT-+-2))
 (9 3 (:REWRITE MOD-+-DISTRIBUTE-2))
 (9 3 (:REWRITE MOD-+-DISTRIBUTE-1))
 (7 1 (:REWRITE DISTRIBUTIVITY))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR MOD-TYPE . 3))
 (4 4 (:LINEAR MOD-TYPE . 1))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(B-MAJ)
(N-ADDER
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CSA-OUT*
 (325 26 (:REWRITE LOGCAR-BITP))
 (243 26 (:DEFINITION BITP))
 (66 6 (:REWRITE LOGXOR-=-0))
 (48 2 (:REWRITE EQUAL-LOGCONS))
 (26 26 (:TYPE-PRESCRIPTION BITP))
 )
(CSA-CARRY*
 (1526 61 (:REWRITE LOGCAR-BITP))
 (1336 57 (:DEFINITION BITP))
 (420 60 (:LINEAR LOGAND-UPPER-BOUND . 2))
 (420 60 (:LINEAR LOGAND-UPPER-BOUND . 1))
 (418 8 (:REWRITE EQUAL-LOGCONS))
 (360 120 (:REWRITE LOGCDR-<-0))
 (280 4 (:REWRITE LOGIOR-=-0))
 (120 120 (:REWRITE DEFAULT-<-2))
 (120 120 (:REWRITE DEFAULT-<-1))
 (78 28 (:REWRITE LOGAND-WITH-MASK))
 (57 57 (:TYPE-PRESCRIPTION BITP))
 (50 50 (:TYPE-PRESCRIPTION LOGMASKP))
 )
(LOGCAR-PLUS
 (822 70 (:LINEAR MOD-TYPE . 2))
 (607 94 (:REWRITE COMMUTATIVITY-OF-*))
 (512 504 (:REWRITE DEFAULT-<-2))
 (512 504 (:REWRITE DEFAULT-<-1))
 (435 435 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (435 435 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (435 435 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (398 126 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (398 126 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (398 126 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (398 126 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (323 48 (:REWRITE DISTRIBUTIVITY))
 (274 272 (:REWRITE DEFAULT-*-2))
 (274 272 (:REWRITE DEFAULT-*-1))
 (198 198 (:REWRITE DEFAULT-+-2))
 (198 198 (:REWRITE DEFAULT-+-1))
 (193 28 (:REWRITE CANCEL-MOD-+-BASIC))
 (126 126 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (119 119 (:REWRITE INTEGERP-+-MINUS-*))
 (70 70 (:LINEAR MOD-TYPE . 3))
 (70 70 (:LINEAR MOD-TYPE . 1))
 (49 7 (:REWRITE CANCEL-MOD-+-3))
 (37 37 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(LOGCDR-PLUS
 (111486 111486 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (111486 111486 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (111486 111486 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (92899 20227 (:REWRITE DEFAULT-TIMES-2))
 (68133 255 (:REWRITE |(floor (+ x r) i)|))
 (65279 20227 (:REWRITE DEFAULT-TIMES-1))
 (55044 4534 (:REWRITE DEFAULT-PLUS-2))
 (50014 17902 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (44267 4965 (:REWRITE RATIONALP-X))
 (40532 199 (:REWRITE FLOOR-ZERO . 3))
 (40190 17902 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (39376 20 (:REWRITE FLOOR-=-X/Y . 4))
 (39097 199 (:REWRITE FLOOR-TYPE-3 . 3))
 (37858 199 (:REWRITE FLOOR-TYPE-4 . 3))
 (34648 199 (:REWRITE CANCEL-FLOOR-+))
 (30159 199 (:REWRITE FLOOR-ZERO . 5))
 (29344 6544 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (29344 6544 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (29173 3552 (:REWRITE ACL2-NUMBERP-X))
 (29111 199 (:REWRITE FLOOR-ZERO . 4))
 (28756 848 (:LINEAR MOD-BOUNDS-2))
 (28724 848 (:LINEAR MOD-BOUNDS-1))
 (28660 5472 (:REWRITE DEFAULT-LESS-THAN-1))
 (27884 6364 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (27884 6364 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (27132 5840 (:REWRITE DEFAULT-LESS-THAN-2))
 (26068 6544 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (26068 6544 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (26068 6544 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (26068 6544 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (26068 6544 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (25248 6364 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (25248 6364 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (25248 6364 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (25248 6364 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (25248 6364 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (22948 848 (:LINEAR MOD-BOUNDED-BY-MODULUS))
 (21937 4534 (:REWRITE DEFAULT-PLUS-1))
 (19989 4813 (:REWRITE REDUCE-RATIONALP-*))
 (19156 199 (:REWRITE FLOOR-=-X/Y . 3))
 (17950 17902 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (17950 17902 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (17902 17902 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (17438 17438 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (17438 17438 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (16772 58 (:LINEAR FLOOR-TYPE-2 . 2))
 (16772 58 (:LINEAR FLOOR-TYPE-2 . 1))
 (16714 58 (:LINEAR FLOOR-TYPE-1 . 2))
 (16714 58 (:LINEAR FLOOR-TYPE-1 . 1))
 (16424 20 (:REWRITE |(equal (floor (+ x y) z) x)|))
 (16123 199 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (16123 199 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (16123 199 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (16123 199 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (15320 199 (:REWRITE FLOOR-=-X/Y . 2))
 (14636 5104 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13916 1485 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (13824 258 (:REWRITE CANCEL-FLOOR-+-BASIC))
 (13700 1485 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (13323 199 (:REWRITE FLOOR-ZERO . 2))
 (13232 1477 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (12806 62 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (12505 12505 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12505 12505 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12505 12505 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12240 199 (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (12240 199 (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (12240 199 (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (11828 424 (:LINEAR MOD-TYPE . 4))
 (11776 199 (:REWRITE FLOOR-CANCEL-*-CONST))
 (11716 424 (:LINEAR MOD-TYPE . 3))
 (11577 4813 (:REWRITE REDUCE-RATIONALP-+))
 (11530 424 (:LINEAR MOD-TYPE . 1))
 (11418 424 (:LINEAR MOD-TYPE . 2))
 (11239 11239 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (11064 5104 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (9964 204 (:REWRITE |(integerp (- x))|))
 (8960 2166 (:REWRITE INTEGERP-+-MINUS-*))
 (8156 8156 (:REWRITE REDUCE-INTEGERP-+))
 (8156 8156 (:REWRITE INTEGERP-MINUS-X))
 (8156 8156 (:META META-INTEGERP-CORRECT))
 (7604 344 (:REWRITE |(* (- x) y)|))
 (6936 62 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (6544 6544 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (6544 6544 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (6476 2744 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6364 6364 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (6364 6364 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (5840 5840 (:REWRITE THE-FLOOR-BELOW))
 (5840 5840 (:REWRITE THE-FLOOR-ABOVE))
 (5618 424 (:LINEAR MOD-BOUNDS-3))
 (5104 5104 (:REWRITE SIMPLIFY-SUMS-<))
 (5104 5104 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5104 5104 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5104 5104 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5104 5104 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5104 5104 (:REWRITE INTEGERP-<-CONSTANT))
 (5104 5104 (:REWRITE CONSTANT-<-INTEGERP))
 (5104 5104 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5104 5104 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5104 5104 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5104 5104 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5104 5104 (:REWRITE |(< c (- x))|))
 (5104 5104 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5104 5104 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5104 5104 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5104 5104 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5104 5104 (:REWRITE |(< (/ x) (/ y))|))
 (5104 5104 (:REWRITE |(< (- x) c)|))
 (5104 5104 (:REWRITE |(< (- x) (- y))|))
 (5027 5027 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4813 4813 (:REWRITE RATIONALP-MINUS-X))
 (4813 4813 (:META META-RATIONALP-CORRECT))
 (3832 84 (:REWRITE MOD-NONNEGATIVE))
 (3830 129 (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (3560 84 (:REWRITE MOD-NEGATIVE . 3))
 (3514 3466 (:REWRITE NORMALIZE-ADDENDS))
 (3458 3458 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3304 384 (:REWRITE DEFAULT-MINUS))
 (2817 365 (:REWRITE DEFAULT-FLOOR-1))
 (2744 2744 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2744 2744 (:REWRITE |(< (/ x) 0)|))
 (2744 2744 (:REWRITE |(< (* x y) 0)|))
 (2576 304 (:DEFINITION RFIX))
 (2374 129 (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
 (2360 2360 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2360 2360 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2360 2360 (:REWRITE |(< 0 (/ x))|))
 (2360 2360 (:REWRITE |(< 0 (* x y))|))
 (2294 74 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (2294 74 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (2294 74 (:REWRITE MOD-X-Y-=-X . 4))
 (2294 74 (:REWRITE MOD-X-Y-=-X . 3))
 (2220 74 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2220 74 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2220 74 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (2220 74 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (2220 74 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2220 74 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1985 1985 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1485 1485 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1485 1485 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1485 1485 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1485 1485 (:REWRITE |(equal c (/ x))|))
 (1485 1485 (:REWRITE |(equal c (- x))|))
 (1485 1485 (:REWRITE |(equal (/ x) c)|))
 (1485 1485 (:REWRITE |(equal (/ x) (/ y))|))
 (1485 1485 (:REWRITE |(equal (- x) c)|))
 (1485 1485 (:REWRITE |(equal (- x) (- y))|))
 (1454 1454 (:REWRITE INTEGERP-/))
 (1368 152 (:REWRITE RATIONALP-/))
 (1366 1366 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1300 74 (:REWRITE MOD-ZERO . 3))
 (1176 84 (:REWRITE MOD-NEGATIVE . 2))
 (1110 74 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (1036 74 (:REWRITE MOD-ZERO . 4))
 (1036 74 (:REWRITE MOD-X-Y-=-X . 2))
 (1036 74 (:REWRITE CANCEL-MOD-+))
 (1036 74 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1036 74 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1036 74 (:DEFINITION ZEROP))
 (756 84 (:REWRITE MOD-TYPE))
 (560 28 (:REWRITE SUM-IS-EVEN . 2))
 (557 5 (:REWRITE NOT-RATIONALP-RATIONALP-UNARY---PLUS))
 (496 16 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (441 441 (:REWRITE |(< (+ c/d x) y)|))
 (441 441 (:REWRITE |(< (+ (- c) x) y)|))
 (387 387 (:REWRITE FOLD-CONSTS-IN-+))
 (344 344 (:REWRITE |(- (* c x))|))
 (306 306 (:REWRITE |(< y (+ (- c) x))|))
 (306 306 (:REWRITE |(< x (+ c/d y))|))
 (280 16 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (261 5 (:REWRITE NOT-RATIONALP-RATIONALP-PLUS))
 (252 252 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (252 252 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (234 22 (:REWRITE INTEGERP-MOD-2))
 (224 16 (:REWRITE EQUAL-*-/-2))
 (199 199 (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (199 199 (:REWRITE |(floor x (- y))| . 2))
 (199 199 (:REWRITE |(floor x (- y))| . 1))
 (199 199 (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (199 199 (:REWRITE |(floor (- x) y)| . 2))
 (199 199 (:REWRITE |(floor (- x) y)| . 1))
 (199 199 (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (191 191 (:LINEAR X*Y>1-POSITIVE))
 (180 180 (:REWRITE DEFAULT-MOD-1))
 (152 16 (:REWRITE MOD-ZERO . 1))
 (129 129 (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (129 129 (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (129 129 (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (129 129 (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (120 16 (:REWRITE MOD-ZERO . 2))
 (108 108 (:REWRITE |(floor x 2)| . 2))
 (88 22 (:REWRITE INTEGERP-MOD-1))
 (88 22 (:REWRITE INTEGERP-MOD))
 (84 84 (:REWRITE MOD-NEGATIVE . 1))
 (80 16 (:REWRITE |(equal (mod (+ x y) z) x)|))
 (74 74 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (74 74 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (74 74 (:REWRITE MOD-CANCEL-*-CONST))
 (74 74 (:REWRITE |(mod x (- y))| . 3))
 (74 74 (:REWRITE |(mod x (- y))| . 2))
 (74 74 (:REWRITE |(mod x (- y))| . 1))
 (74 74 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (74 74 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (74 74 (:REWRITE |(mod (- x) y)| . 3))
 (74 74 (:REWRITE |(mod (- x) y)| . 2))
 (74 74 (:REWRITE |(mod (- x) y)| . 1))
 (74 74 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (74 74 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (70 70 (:REWRITE <-*-0))
 (70 70 (:REWRITE <-*-/-LEFT))
 (70 70 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (70 70 (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (56 56 (:REWRITE |(mod x 2)| . 2))
 (48 48 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (48 16 (:REWRITE |(- (- x))|))
 (32 32 (:REWRITE |(equal (+ (- c) x) y)|))
 (28 28 (:DEFINITION B-MAJ))
 (16 16 (:REWRITE EQUAL-CONSTANT-+))
 (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE |(+ x (- x))|))
 )
(LOGCAR-PLUS-SIMPLE
 (13 3 (:REWRITE LOGCAR-BITP))
 (7 3 (:DEFINITION BITP))
 (3 3 (:TYPE-PRESCRIPTION BITP))
 (3 1 (:REWRITE NORMALIZE-EQUAL-0))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LOGCDR-PLUS-SIMPLE
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE LOGCAR-BITP))
 (10 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:DEFINITION BITP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(STANDARD-ADDER-ADDS
 (1043 1043 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (750 214 (:REWRITE LOGCAR-BITP))
 (468 38 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (323 172 (:REWRITE DEFAULT-<-2))
 (221 148 (:REWRITE DEFAULT-+-2))
 (193 172 (:REWRITE DEFAULT-<-1))
 (184 148 (:REWRITE DEFAULT-+-1))
 (109 88 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (76 57 (:REWRITE UNSIGNED-BYTE-P-<))
 (52 52 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (26 26 (:REWRITE EQUAL-CONSTANT-+))
 (21 21 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (21 21 (:REWRITE EXPONENTS-ADD))
 )
(THREE-BITVECTOR-INDUCTION
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(UNSIGNED-BYTE-P-CSA-OUT
 (937 76 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (205 205 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (205 106 (:REWRITE DEFAULT-<-2))
 (152 114 (:REWRITE UNSIGNED-BYTE-P-<))
 (127 106 (:REWRITE DEFAULT-<-1))
 (126 15 (:REWRITE LOGCAR-BITP))
 (102 102 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (78 15 (:DEFINITION BITP))
 (74 60 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (39 13 (:REWRITE <-0-+-NEGATIVE-1))
 (38 38 (:REWRITE DEFAULT-+-2))
 (38 38 (:REWRITE DEFAULT-+-1))
 (15 15 (:TYPE-PRESCRIPTION BITP))
 (14 14 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (14 14 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UNSIGNED-BYTE-P-CSA-CARRY
 (937 76 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (205 205 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (205 106 (:REWRITE DEFAULT-<-2))
 (152 114 (:REWRITE UNSIGNED-BYTE-P-<))
 (129 18 (:REWRITE LOGCAR-BITP))
 (127 106 (:REWRITE DEFAULT-<-1))
 (102 102 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (78 15 (:DEFINITION BITP))
 (74 60 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (39 13 (:REWRITE <-0-+-NEGATIVE-1))
 (38 38 (:REWRITE DEFAULT-+-2))
 (38 38 (:REWRITE DEFAULT-+-1))
 (15 15 (:TYPE-PRESCRIPTION BITP))
 (14 14 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (14 14 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CSA-ADDER-INDUCTION
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CSA-ADDER-REC
 (61992 61992 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (39381 3410 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (13843 261 (:REWRITE UNSIGNED-BYTE-P-CSA-OUT))
 (13721 5432 (:REWRITE DEFAULT-<-2))
 (13184 6150 (:REWRITE DEFAULT-+-2))
 (9930 6150 (:REWRITE DEFAULT-+-1))
 (8389 5432 (:REWRITE DEFAULT-<-1))
 (7401 6092 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (6462 4757 (:REWRITE UNSIGNED-BYTE-P-<))
 (4564 4564 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (2295 765 (:REWRITE <-0-+-NEGATIVE-1))
 (1980 18 (:REWRITE UNSIGNED-BYTE-P-LOGCONS))
 (1316 1309 (:REWRITE EXPONENTS-ADD))
 (1308 1308 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (27 1 (:REWRITE <-*-/-RIGHT-COMMUTED))
 (7 3 (:REWRITE DEFAULT-*-2))
 (6 1 (:REWRITE ZP-OPEN))
 (4 3 (:REWRITE DEFAULT-*-1))
 (4 1 (:REWRITE COMMUTATIVITY-OF-*))
 )
(CSA-IS-ADDER
 (11 9 (:REWRITE DEFAULT-+-2))
 (11 9 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(CSA-IS-WORD-ADDER
 (11 3 (:REWRITE REDUCE-WORD))
 (6 5 (:REWRITE DEFAULT-+-2))
 (6 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (5 5 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (5 3 (:REWRITE FERMENT-WORD-TO-ADD))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(ADD-N-SHIFT
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(WORD-ADD-N-SHIFT
 (34 22 (:REWRITE DEFAULT-+-2))
 (34 22 (:REWRITE DEFAULT-+-1))
 (18 18 (:TYPE-PRESCRIPTION SHIFTER))
 (18 6 (:REWRITE FERMENT-WORD-TO-ADD))
 (10 10 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (10 10 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE ZP-OPEN))
 )
(LOGBIT-1-OR-0)
(SHIFTER-TO-MULTIPLY
 (15 6 (:REWRITE DEFAULT-*-2))
 (12 6 (:REWRITE DEFAULT-*-1))
 (10 2 (:REWRITE REDUCE-WORD))
 (6 6 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (4 4 (:TYPE-PRESCRIPTION WORD-P))
 (2 2 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (2 2 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ADD-N-SHIFT-MULT-REC
 (1422 67 (:DEFINITION UNSIGNED-BYTE-P))
 (1207 38 (:DEFINITION INTEGER-RANGE-P))
 (1038 58 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (611 611 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (310 141 (:REWRITE DEFAULT-+-2))
 (289 141 (:REWRITE DEFAULT-<-2))
 (241 198 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (235 76 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (229 62 (:REWRITE DEFAULT-*-2))
 (222 38 (:LINEAR EXPT->-1))
 (185 62 (:REWRITE DEFAULT-*-1))
 (179 47 (:REWRITE LOGBIT-1-OR-0))
 (178 141 (:REWRITE DEFAULT-+-1))
 (141 141 (:REWRITE DEFAULT-<-1))
 (140 8 (:REWRITE INTEGERP-+-MINUS-*))
 (131 27 (:REWRITE REDUCE-WORD))
 (118 89 (:REWRITE UNSIGNED-BYTE-P-<))
 (100 100 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
 (96 32 (:REWRITE FOLD-CONSTS-IN-+))
 (90 30 (:REWRITE <-0-+-NEGATIVE-1))
 (76 16 (:REWRITE ZP-OPEN))
 (74 18 (:REWRITE FERMENT-WORD-TO-ADD))
 (67 67 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (52 52 (:TYPE-PRESCRIPTION WORD-P))
 (43 43 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (26 26 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (26 26 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (14 14 (:REWRITE FOLD-CONSTS-IN-*))
 )
(ADD-N-SHIFT-MULT
 (50 6 (:REWRITE LOGHEAD-IDENTITY))
 (29 5 (:DEFINITION UNSIGNED-BYTE-P))
 (24 5 (:DEFINITION INTEGER-RANGE-P))
 (15 5 (:LINEAR X*Y>1-POSITIVE))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (8 8 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-<))
 (5 1 (:REWRITE REDUCE-WORD))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(CSA-1-1-SUM
 (30 13 (:REWRITE DEFAULT-+-2))
 (26 13 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (5 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (3 3 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-1-2-SUM
 (30 13 (:REWRITE DEFAULT-+-2))
 (26 13 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (5 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (3 3 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-1-3-SUM
 (30 13 (:REWRITE DEFAULT-+-2))
 (26 13 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (5 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (3 3 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-1-4-SUM
 (30 13 (:REWRITE DEFAULT-+-2))
 (26 13 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (5 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (3 3 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-1-5-SUM
 (30 13 (:REWRITE DEFAULT-+-2))
 (26 13 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (5 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (3 3 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-2-1&2-SUM-HINT-1
 (884 225 (:REWRITE DEFAULT-+-2))
 (450 225 (:REWRITE DEFAULT-+-1))
 (154 154 (:REWRITE FOLD-CONSTS-IN-+))
 (72 24 (:REWRITE REDUCE-WORD))
 (14 14 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (14 14 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (3 3 (:TYPE-PRESCRIPTION SHIFT-1))
 )
(CSA-2-1&2-SUM-HINT-2
 (42 18 (:REWRITE DEFAULT-+-2))
 (36 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE REDUCE-WORD))
 (6 6 (:TYPE-PRESCRIPTION CSA-1-3-OUT))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (5 5 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-2-1&2-SUM
 (1047 279 (:REWRITE DEFAULT-+-2))
 (558 279 (:REWRITE DEFAULT-+-1))
 (190 190 (:REWRITE FOLD-CONSTS-IN-+))
 (160 32 (:REWRITE REDUCE-WORD))
 (38 38 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (38 38 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(CSA-2-3-SUM-HINT
 (46 19 (:REWRITE DEFAULT-+-2))
 (38 19 (:REWRITE DEFAULT-+-1))
 (15 6 (:REWRITE FERMENT-WORD-TO-ADD))
 (12 4 (:REWRITE REDUCE-WORD))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (4 4 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 )
(CSA-2-3-SUM
 (77 31 (:REWRITE DEFAULT-+-2))
 (62 31 (:REWRITE DEFAULT-+-1))
 (31 8 (:REWRITE FERMENT-WORD-TO-ADD))
 (30 6 (:REWRITE REDUCE-WORD))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (10 10 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-3-1&2-SUM-HINT-1
 (42 18 (:REWRITE DEFAULT-+-2))
 (36 18 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE REDUCE-WORD))
 (6 6 (:TYPE-PRESCRIPTION CSA-2-1-OUT))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (5 5 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-3-1&2-SUM-HINT-2
 (672 164 (:REWRITE DEFAULT-+-2))
 (328 164 (:REWRITE DEFAULT-+-1))
 (119 119 (:REWRITE FOLD-CONSTS-IN-+))
 (18 6 (:REWRITE REDUCE-WORD))
 (5 5 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (5 5 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(CSA-3-1&2-SUM
 (1496 331 (:REWRITE DEFAULT-+-2))
 (662 331 (:REWRITE DEFAULT-+-1))
 (245 245 (:REWRITE FOLD-CONSTS-IN-+))
 (140 28 (:REWRITE REDUCE-WORD))
 (34 34 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (34 34 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(CSA-4-1-SUM
 (7 7 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (7 7 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (6 5 (:REWRITE DEFAULT-+-2))
 (6 5 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 )
(CSA-4-2-SUM
 (7 7 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (7 7 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (6 5 (:REWRITE DEFAULT-+-2))
 (6 5 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE REDUCE-WORD))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 )
(CSA-5-1-SUM-HINT-1
 (34 13 (:REWRITE DEFAULT-+-2))
 (26 13 (:REWRITE DEFAULT-+-1))
 (15 6 (:REWRITE FERMENT-WORD-TO-ADD))
 (12 4 (:REWRITE REDUCE-WORD))
 (8 8 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (8 8 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 )
(CSA-5-1-SUM-HINT-2
 (82 68 (:REWRITE DEFAULT-+-2))
 (78 68 (:REWRITE DEFAULT-+-1))
 (46 46 (:REWRITE FOLD-CONSTS-IN-+))
 (30 10 (:REWRITE REDUCE-WORD))
 (11 11 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (11 11 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION SHIFT-1))
 )
(CSA-5-1-SUM
 (101 57 (:REWRITE DEFAULT-+-2))
 (85 57 (:REWRITE DEFAULT-+-1))
 (65 13 (:REWRITE REDUCE-WORD))
 (34 34 (:REWRITE FOLD-CONSTS-IN-+))
 (25 25 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (25 25 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(CSA-6-1-SUM
 (17 13 (:REWRITE DEFAULT-+-2))
 (16 13 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (7 7 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (6 2 (:REWRITE REDUCE-WORD))
 (3 3 (:TYPE-PRESCRIPTION SHIFT-1))
 (2 2 (:TYPE-PRESCRIPTION CSA-5-1-OUT))
 (2 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (1 1 (:TYPE-PRESCRIPTION CSA-OUT))
 (1 1 (:TYPE-PRESCRIPTION CSA-4-1-OUT))
 )
(CSA-3-ALL-SUM-HINT
 (3777 580 (:REWRITE DEFAULT-+-2))
 (1160 580 (:REWRITE DEFAULT-+-1))
 (486 486 (:REWRITE FOLD-CONSTS-IN-+))
 (84 28 (:REWRITE REDUCE-WORD))
 (16 16 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (16 16 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(CSA-3-ALL-SUM
 (3609 565 (:REWRITE DEFAULT-+-2))
 (1130 565 (:REWRITE DEFAULT-+-1))
 (476 476 (:REWRITE FOLD-CONSTS-IN-+))
 (110 22 (:REWRITE REDUCE-WORD))
 (26 26 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (26 26 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(ML1-SUMS-SUM
 (3525 575 (:REWRITE DEFAULT-+-2))
 (1149 575 (:REWRITE DEFAULT-+-1))
 (448 448 (:REWRITE FOLD-CONSTS-IN-+))
 (261 48 (:REWRITE FERMENT-WORD-TO-ADD))
 (37 37 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (37 37 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 )
(ML2-SUMS-SUM
 (12 11 (:REWRITE DEFAULT-+-2))
 (12 11 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (7 7 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (6 2 (:REWRITE REDUCE-WORD))
 (2 2 (:REWRITE FERMENT-WORD-TO-ADD))
 (1 1 (:TYPE-PRESCRIPTION SHIFT-1))
 )
(CORRECTNESS-OF-MULTIPLIER
 (22 6 (:REWRITE DEFAULT-+-2))
 (12 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE WORD-LISTP-MEMBERP-EQUAL))
 (4 4 (:REWRITE WORD-LISTP-MEMBER-EQUAL))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
