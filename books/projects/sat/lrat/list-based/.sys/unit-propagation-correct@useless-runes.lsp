(LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER
 (19 2 (:DEFINITION MEMBER-EQUAL))
 (12 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (6 6 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (4 4 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (4 1 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (3 3 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (3 1 (:REWRITE LRAT::NEGATE-NEGATE))
 (2 2 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE LRAT::MINUS-MINUS))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET
 (31 3 (:DEFINITION MEMBER-EQUAL))
 (24 4 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (23 1 (:DEFINITION SUBSETP-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (8 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (6 6 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE LRAT::SUBSETP-TRANSITIVE))
 (2 2 (:REWRITE LRAT::IS-UNIT-CLAUSE-T-MONOTONE))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(LRAT::SUBSETP-UNION-EQUAL-2
 (284 47 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (221 7 (:DEFINITION UNION-EQUAL))
 (142 142 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (83 17 (:REWRITE LRAT::SUBSETP-TRANSITIVE))
 (72 18 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (71 71 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (64 64 (:REWRITE DEFAULT-CAR))
 (51 51 (:REWRITE DEFAULT-CDR))
 (24 6 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (13 13 (:REWRITE LRAT::IS-UNIT-CLAUSE-T-MONOTONE))
 (3 3 (:TYPE-PRESCRIPTION UNION-EQUAL))
 )
(LRAT::NOT-CONFLICTING-LITERALSP-SUBSETP
 (328 24 (:DEFINITION MEMBER-EQUAL))
 (240 28 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (200 200 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (172 43 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (144 18 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (140 24 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (100 100 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (75 5 (:DEFINITION LRAT::LITERAL-LISTP))
 (47 47 (:REWRITE DEFAULT-CDR))
 (44 44 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 5 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE LRAT::SUBSETP-TRANSITIVE))
 (8 8 (:REWRITE LRAT::IS-UNIT-CLAUSE-T-MONOTONE))
 )
(LRAT::UNION-PRESERVES-SUBSETP-2
 (783 113 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (510 29 (:REWRITE LRAT::SUBSETP-UNION-EQUAL-2))
 (388 388 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (275 74 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (208 200 (:REWRITE DEFAULT-CAR))
 (194 194 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (188 182 (:REWRITE DEFAULT-CDR))
 (161 3 (:REWRITE LRAT::CONS-PRESERVES-SUBSETP))
 (98 98 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (88 12 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (32 32 (:REWRITE LRAT::IS-UNIT-CLAUSE-T-MONOTONE))
 (24 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 )
(LRAT::CONFLICTING-LITERALSP-PRESERVED-BY-UNION-EQUAL-CONS-2
 (1725 198 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (1678 131 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (1270 1270 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (1264 268 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (837 76 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (635 635 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (599 95 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (402 402 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (290 276 (:REWRITE DEFAULT-CAR))
 (285 257 (:REWRITE DEFAULT-CDR))
 (154 64 (:REWRITE DEFAULT-UNARY-MINUS))
 (131 131 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (120 20 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 (87 76 (:REWRITE LRAT::CONTRADICTION-IMPLIES-CONFLICTING-LITERALSP))
 (76 76 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-SUBSETP))
 (63 36 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(LRAT::CONFLICTING-LITERALSP-UNION-WHEN-MEMBER
 (18859 2736 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (15190 1521 (:REWRITE LRAT::SUBSETP-EQUAL-CONS-LEMMA))
 (15190 1521 (:REWRITE LRAT::CONS-PRESERVES-SUBSETP))
 (12873 12873 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (11003 10784 (:REWRITE DEFAULT-CAR))
 (10853 10333 (:REWRITE DEFAULT-CDR))
 (9433 2168 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (8753 8753 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (6552 6552 (:REWRITE LRAT::SUBSETP-TRANSITIVE))
 (6436 6436 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (6050 736 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (2210 396 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (1952 480 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 (1118 178 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (561 182 (:REWRITE DEFAULT-UNARY-MINUS))
 (500 291 (:REWRITE LRAT::CONTRADICTION-IMPLIES-CONFLICTING-LITERALSP))
 (256 133 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (110 110 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (110 22 (:DEFINITION TRUE-LISTP))
 (34 34 (:REWRITE LRAT::SUBSETP-EQUAL-REFLEXIVE))
 (1 1 (:REWRITE LRAT::MINUS-MINUS))
 )
(LRAT::EVALUATE-CLAUSE-UNION-EQUAL-CONS-2
 (1951 336 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (1036 1036 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (831 27 (:DEFINITION UNION-EQUAL))
 (752 116 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (518 518 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (499 499 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (456 114 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (313 313 (:REWRITE DEFAULT-CAR))
 (252 252 (:REWRITE DEFAULT-CDR))
 (198 57 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (152 19 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (116 116 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (92 23 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 (60 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 )
(LRAT::NOT-CONFLICTING-LITERALSP-UNION-LEMMA
 (1794 238 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (1318 1318 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (1013 30 (:DEFINITION UNION-EQUAL))
 (978 192 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (809 105 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (659 659 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (613 81 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (407 407 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (407 110 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (345 329 (:REWRITE DEFAULT-CAR))
 (327 300 (:REWRITE DEFAULT-CDR))
 (158 59 (:REWRITE DEFAULT-UNARY-MINUS))
 (143 7 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT-REC-LEMMA))
 (128 16 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (112 28 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (105 105 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (104 4 (:REWRITE LRAT::CONFLICTING-LITERALSP-UNION-WHEN-MEMBER))
 (66 33 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (49 7 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT-REC))
 (46 46 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-SUBSETP))
 (46 46 (:REWRITE LRAT::CONTRADICTION-IMPLIES-CONFLICTING-LITERALSP))
 (20 5 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 (16 16 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 )
(LRAT::EVALUATE-CLAUSE-UNION-EQUAL-NIL
 (551 95 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (306 306 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (182 41 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (145 145 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (136 34 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (135 135 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (108 18 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (98 7 (:DEFINITION UNION-EQUAL))
 (71 71 (:REWRITE DEFAULT-CAR))
 (56 56 (:REWRITE DEFAULT-CDR))
 (56 17 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (48 12 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (41 41 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (32 32 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (32 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE LRAT::EVALUATE-CLAUSE-UNION-EQUAL-CONS-2))
 )
(LRAT::CONFLICTING-LITERALSP-UNION-EQUAL-NIL
 (525 53 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (385 45 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (384 384 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (370 79 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (274 33 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (187 187 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (141 32 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (127 127 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (87 82 (:REWRITE DEFAULT-CDR))
 (82 79 (:REWRITE DEFAULT-CAR))
 (45 45 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (40 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 3 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 (33 33 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-SUBSETP))
 (33 33 (:REWRITE LRAT::CONTRADICTION-IMPLIES-CONFLICTING-LITERALSP))
 (32 8 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (20 20 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (20 20 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(LRAT::NOT-CONFLICTING-LITERALSP-UNION
 (167 14 (:DEFINITION MEMBER-EQUAL))
 (136 18 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (124 2 (:DEFINITION LRAT::EVALUATE-CLAUSE))
 (102 102 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (94 2 (:DEFINITION LRAT::EVALUATE-LITERAL))
 (72 18 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (64 3 (:DEFINITION UNION-EQUAL))
 (60 10 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (50 50 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (48 8 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (30 30 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (25 25 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (16 4 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (15 1 (:DEFINITION LRAT::LITERAL-LISTP))
 (12 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (7 1 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT-REC))
 (6 6 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-SUBSETP))
 (6 6 (:REWRITE LRAT::CONTRADICTION-IMPLIES-CONFLICTING-LITERALSP))
 (5 1 (:DEFINITION LRAT::NEGATE-CLAUSE-OR-ASSIGNMENT-REC))
 (4 4 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 (4 1 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT-REC-LEMMA))
 (2 2 (:TYPE-PRESCRIPTION LRAT::NEGATE-CLAUSE-OR-ASSIGNMENT-REC))
 (2 2 (:DEFINITION LRAT::UNDEFP$INLINE))
 )
(LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION
 (2319 180 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (1976 117 (:DEFINITION MEMBER-EQUAL))
 (1924 344 (:REWRITE LRAT::BACKCHAIN-TO-CLAUSE-OR-ASSIGNMENT-P))
 (1237 21 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (940 2 (:DEFINITION UNION-EQUAL))
 (725 61 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (655 89 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (554 2 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT))
 (470 1 (:DEFINITION LRAT::EVALUATE-CLAUSE))
 (368 1 (:DEFINITION LRAT::EVALUATE-LITERAL))
 (366 366 (:REWRITE DEFAULT-CDR))
 (303 303 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (272 272 (:REWRITE DEFAULT-CAR))
 (182 2 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (106 106 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-SUBSETP))
 (106 106 (:REWRITE LRAT::CONTRADICTION-IMPLIES-CONFLICTING-LITERALSP))
 (96 49 (:REWRITE DEFAULT-UNARY-MINUS))
 (89 89 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (65 65 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (47 47 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 (1 1 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-IS-NOT-CONTRADICTORY))
 (1 1 (:DEFINITION LRAT::UNDEFP$INLINE))
 )
(LRAT::SUBSETP-UNION-1
 (399 56 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (198 198 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (138 10 (:REWRITE LRAT::SUBSETP-UNION-EQUAL-2))
 (131 35 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (120 96 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (99 99 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (96 93 (:REWRITE DEFAULT-CAR))
 (74 3 (:REWRITE LRAT::CONS-PRESERVES-SUBSETP))
 (61 61 (:REWRITE DEFAULT-CDR))
 (56 8 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-UNION-EQUAL))
 (36 3 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CONS))
 (30 28 (:REWRITE LRAT::SUBSETP-TRANSITIVE))
 (20 20 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (10 10 (:REWRITE LRAT::IS-UNIT-CLAUSE-T-MONOTONE))
 )
(LRAT::UNIT-PROPAGATION-CORRECT-1
 (40 1 (:DEFINITION UNION-EQUAL))
 (20 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (18 1 (:DEFINITION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION LRAT::CLAUSE-OR-ASSIGNMENT-P))
 (8 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-NEGATE-CLAUSE-OR-ASSIGNMENT))
 (8 1 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (7 1 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT))
 (6 6 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (4 1 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (3 3 (:REWRITE LRAT::SUBSETP-EQUAL-REFLEXIVE))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION LRAT::NEGATE-CLAUSE-OR-ASSIGNMENT))
 (2 2 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (2 2 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (2 2 (:REWRITE LRAT::FORMULA-TRUEP-NECC))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(LRAT::UNIT-PROPAGATION-CORRECT-2
 (476 1 (:DEFINITION LRAT::UNIT-PROPAGATION))
 (340 5 (:DEFINITION LRAT::EVALUATE-LITERAL))
 (325 4 (:DEFINITION LRAT::EVALUATE-CLAUSE))
 (298 1 (:DEFINITION LRAT::IS-UNIT-CLAUSE))
 (233 14 (:DEFINITION MEMBER-EQUAL))
 (205 26 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (204 2 (:REWRITE LRAT::EVALUATE-CLAUSE-NIL-IMPLIES-IS-UNIT-CLAUSE-T))
 (95 10 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT))
 (63 63 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (62 14 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (59 59 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (59 17 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (56 56 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (55 15 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (50 1 (:DEFINITION UNION-EQUAL))
 (37 37 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (37 1 (:DEFINITION ADD-TO-SET-EQUAL))
 (30 30 (:REWRITE DEFAULT-CDR))
 (29 29 (:REWRITE DEFAULT-CAR))
 (26 8 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (17 17 (:TYPE-PRESCRIPTION LRAT::NEGATE-CLAUSE-OR-ASSIGNMENT))
 (16 4 (:REWRITE LRAT::UNIT-PROPAGATION-IDENTITY))
 (15 1 (:DEFINITION LRAT::FORMULA-P))
 (14 14 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (13 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 2 (:REWRITE LRAT::EVALUATE-CLAUSE-T-IMPLIES-NOT-IS-UNIT-CLAUSE))
 (10 10 (:TYPE-PRESCRIPTION LRAT::FORMULA-TRUEP))
 (10 1 (:DEFINITION LRAT::MY-HONS-GET$NOTINLINE))
 (9 1 (:DEFINITION HONS-GET))
 (8 8 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 (8 1 (:DEFINITION HONS-ASSOC-EQUAL))
 (7 1 (:REWRITE LRAT::UNIT-PROPAGATION-IMPLIES-UNSAT))
 (6 6 (:TYPE-PRESCRIPTION LRAT::TRUE-LISTP-LOOKUP-FORMULA-INDEX))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE LRAT::TRUTH-MONOTONE))
 (5 5 (:DEFINITION LRAT::UNDEFP$INLINE))
 (4 2 (:DEFINITION NULL))
 (3 3 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (3 3 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-IS-NOT-CONTRADICTORY))
 (3 1 (:TYPE-PRESCRIPTION LRAT::LITERALP-IS-UNIT-CLAUSE))
 (3 1 (:DEFINITION POSP))
 (2 2 (:TYPE-PRESCRIPTION NULL))
 (1 1 (:REWRITE LRAT::IS-UNIT-CLAUSE-SUPERSET))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:DEFINITION HONS-EQUAL))
 )
(LRAT::UNIT-PROPAGATION-CORRECT
 (100 2 (:DEFINITION UNION-EQUAL))
 (74 2 (:REWRITE LRAT::MEMBER-EQUAL-NEGATE-CLAUSE-OR-ASSIGNMENT))
 (67 6 (:DEFINITION MEMBER-EQUAL))
 (48 1 (:DEFINITION LRAT::EVALUATE-CLAUSE))
 (43 10 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-HAS-LITERALS))
 (38 6 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER))
 (36 1 (:DEFINITION LRAT::EVALUATE-LITERAL))
 (27 27 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (17 17 (:TYPE-PRESCRIPTION LRAT::LITERALP))
 (17 17 (:REWRITE LRAT::MEMBER-EQUAL-MONOTONE))
 (11 11 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE LRAT::UNIT-PROPAGATION-MONOTONICITY))
 (6 6 (:REWRITE LRAT::NOT-CONFLICTING-LITERALSP-IMPLIES-NEGATE-IS-NOT-MEMBER-SUBSET))
 (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-FORWARD))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-CDR))
 (2 2 (:REWRITE LRAT::TRUTH-MONOTONE-CLAUSE))
 (2 2 (:REWRITE LRAT::TRUTH-MONOTONE))
 (2 2 (:REWRITE LRAT::SUBSETP-PRESERVES-EVALUATE-CLAUSE-NIL))
 (2 2 (:REWRITE LRAT::FORMULA-TRUEP-NECC))
 (2 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-NEGATE-CLAUSE-OR-ASSIGNMENT))
 (2 2 (:REWRITE LRAT::CLAUSE-OR-ASSIGNMENT-P-IS-NOT-CONTRADICTORY))
 (1 1 (:DEFINITION LRAT::UNDEFP$INLINE))
 )
