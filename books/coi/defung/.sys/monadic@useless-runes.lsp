(|LACK-base|)
(LACK-DEFAULT)
(|LACK-test|
 (2 2 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 )
(|iLACK|
 (4 4 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 )
(|iLACK-DOMAIN|
 (4 4 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 )
(|ARB-iLACK-INDEX-THM|)
(|iLACK-MONO-DETERM|
 (110 110 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (17 17 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 )
(|iLACK-DOMAIN-MONOTONE|)
(|iLACK-DOMAIN-MONOTONE-CONTRAPOSITIVE|)
(|iLACK-DOMAIN-LOWER-BOUND|)
(|iLACK-MIN-INDEX|)
(|NATP-iLACK-MIN-INDEX|)
(|iLACK-DOMAIN-MIN-INDEX|)
(|iLACK-MIN-INDEX-BOUND|)
(|iLACK-MIN-INDEX-SMALLEST|)
(LACK-MEASURE)
(LACK-MEASURE-TYPE)
(LACK-MEASURE-PROPERTY)
(LACK-MEASURE-SMALLEST)
(|REPLACE-ARB-iLACK-INDEX-BY-LACK-MEASURE|
 (4 4 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (4 4 (:TYPE-PRESCRIPTION DEFUNG::NOT-TRUE-FROM-NOT-X))
 (4 4 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (4 1 (:LINEAR LACK-MEASURE-SMALLEST))
 )
(|REPLACE-ARB-iLACK-INDEX-BY-LACK-MEASURE-2|)
(|REPLACE-iLACK-DOMAIN-INDEX-BY-LACK-MEASURE|
 (2 2 (:REWRITE |iLACK-DOMAIN-MONOTONE|))
 )
(LACK)
(LACK-DOMAIN)
(NOT-LACK-DOMAIN-IMPLIES-ZERO-LACK-MEASURE
 (2 1 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 )
(LACK-MEASURE-BODY
 (4 4 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 )
(LACK-MEASURE-DEFINITION
 (469 469 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (129 85 (:LINEAR LACK-MEASURE-SMALLEST))
 (119 119 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (57 21 (:REWRITE DEFUNG::TRUE-FROM-X))
 (57 21 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (21 21 (:REWRITE DEFUNG::QUOTED-TRUE))
 )
(LACK-DOMAIN-DEFINITION
 (482 482 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (66 33 (:REWRITE DEFUNG::TRUE-FROM-X))
 (66 33 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (33 33 (:REWRITE DEFUNG::QUOTED-TRUE))
 )
(LACK-DEFINITION
 (189 189 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (81 66 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (64 26 (:REWRITE |REPLACE-ARB-iLACK-INDEX-BY-LACK-MEASURE|))
 (41 9 (:REWRITE |iLACK-DOMAIN-MONOTONE|))
 (26 13 (:REWRITE DEFUNG::TRUE-FROM-X))
 (26 13 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (13 13 (:REWRITE DEFUNG::QUOTED-TRUE))
 )
(LACK-INDUCTION
 (713 23 (:DEFINITION LACK-DEFINITION))
 (569 569 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (172 172 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (90 30 (:TYPE-PRESCRIPTION DEFUNG::NATP-MAX))
 (76 38 (:REWRITE DEFUNG::TRUE-FROM-X))
 (76 38 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (38 38 (:REWRITE DEFUNG::QUOTED-TRUE))
 (23 23 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 )
(LACK-INDUCTION-IS-LACK-DOMAIN
 (183 183 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (172 10 (:DEFINITION LACK-DEFINITION))
 (18 18 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 (18 9 (:REWRITE DEFUNG::TRUE-FROM-X))
 (18 9 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (9 9 (:REWRITE DEFUNG::QUOTED-TRUE))
 (8 4 (:DEFINITION NOT))
 )
(LACK-INDUCTION-RULE)
(OPEN-LACK-DOMAIN
 (32 2 (:DEFINITION LACK-DEFINITION))
 (17 17 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (4 4 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (2 2 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 )
(LACK-DOMAIN-TRUE
 (1 1 (:REWRITE OPEN-LACK-DOMAIN))
 )
(OPEN-LACK-BASE)
(OPEN-LACK-INDUCTION
 (24 24 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (20 8 (:REWRITE LACK-DOMAIN-TRUE))
 (9 9 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (8 8 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 (2 1 (:REWRITE DEFUNG::TRUE-FROM-X))
 (2 1 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (1 1 (:REWRITE DEFUNG::QUOTED-TRUE))
 )
(OPEN-LACK-MEASURE-BASE)
(OPEN-LACK-MEASURE-INDUCTION
 (44 2 (:DEFINITION LACK-DEFINITION))
 (27 27 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (8 4 (:REWRITE LACK-DOMAIN-TRUE))
 (4 4 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (2 2 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 )
(INTEGERP-INTEGERP-IMPLIES-INTEGERP-LACK
 (175 175 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (45 45 (:REWRITE O-INFP->NEQ-0))
 (45 45 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (45 45 (:META *META*-UNHIDE-HIDE))
 (28 28 (:REWRITE DEFAULT-+-2))
 (28 28 (:REWRITE DEFAULT-+-1))
 )
(ACK-DEFAULT)
(XACK)
(XACK
 (966 65 (:REWRITE OPEN-LACK-INDUCTION))
 (601 591 (:REWRITE O-INFP->NEQ-0))
 (570 570 (:REWRITE DEFAULT-+-2))
 (570 570 (:REWRITE DEFAULT-+-1))
 (500 500 (:META *META*-UNHIDE-HIDE))
 (195 65 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 (131 73 (:REWRITE DEFUNG::TRUE-FROM-X))
 (73 73 (:REWRITE DEFUNG::QUOTED-TRUE))
 (42 31 (:REWRITE DEFAULT-CAR))
 (40 29 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION O-FINP))
 (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 )
(ACK-DOMAIN)
(ACK)
(ACK-MEASURE)
(ACK-DEFINITION
 (1746 481 (:REWRITE O-INFP->NEQ-0))
 (1019 507 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (785 785 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (759 759 (:TYPE-PRESCRIPTION O-FINP))
 (759 253 (:REWRITE O-FIRST-EXPT-O-INFP))
 (512 512 (:TYPE-PRESCRIPTION BOOLEANP))
 (506 253 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (494 494 (:REWRITE DEFAULT-+-1))
 (447 447 (:META *META*-UNHIDE-HIDE))
 (225 225 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (66 22 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (44 22 (:REWRITE DEFUNG::TRUE-FROM-X))
 (22 22 (:REWRITE DEFUNG::QUOTED-TRUE))
 (5 1 (:REWRITE DEFUNG::NATP-FIX))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ACK-DOMAIN-DEFINITION
 (945 265 (:REWRITE O-INFP->NEQ-0))
 (561 285 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (558 558 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (408 408 (:TYPE-PRESCRIPTION O-FINP))
 (408 136 (:REWRITE O-FIRST-EXPT-O-INFP))
 (276 276 (:TYPE-PRESCRIPTION BOOLEANP))
 (272 136 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (262 262 (:REWRITE DEFAULT-+-1))
 (235 235 (:META *META*-UNHIDE-HIDE))
 (136 136 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (54 18 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (36 18 (:REWRITE DEFUNG::TRUE-FROM-X))
 (18 18 (:REWRITE DEFUNG::QUOTED-TRUE))
 (10 2 (:REWRITE DEFUNG::NATP-FIX))
 (6 2 (:DEFINITION NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ACK-MEASURE-DEFINITION
 (3494 161 (:REWRITE OPEN-LACK-BASE))
 (1762 111 (:REWRITE LACK-DOMAIN-TRUE))
 (1485 400 (:REWRITE O-INFP->NEQ-0))
 (874 420 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (756 756 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (651 651 (:TYPE-PRESCRIPTION O-FINP))
 (651 217 (:REWRITE O-FIRST-EXPT-O-INFP))
 (462 21 (:REWRITE OPEN-LACK-MEASURE-BASE))
 (434 434 (:TYPE-PRESCRIPTION BOOLEANP))
 (434 217 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (409 409 (:REWRITE DEFAULT-+-1))
 (370 370 (:META *META*-UNHIDE-HIDE))
 (368 21 (:REWRITE OPEN-LACK-MEASURE-INDUCTION))
 (193 193 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (51 17 (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
 (34 17 (:REWRITE DEFUNG::TRUE-FROM-X))
 (21 6 (:DEFINITION |LACK-base|))
 (17 17 (:REWRITE DEFUNG::QUOTED-TRUE))
 (17 9 (:REWRITE DEFAULT-<-1))
 (16 9 (:REWRITE DEFAULT-<-2))
 (5 1 (:REWRITE DEFUNG::NATP-FIX))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ACK-INDUCTION
 (5239 130 (:DEFINITION ACK-DEFINITION))
 (2697 1506 (:REWRITE DEFAULT-+-2))
 (2115 496 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 (1506 1506 (:REWRITE DEFAULT-+-1))
 (1097 1097 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (552 302 (:REWRITE O-INFP->NEQ-0))
 (402 302 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (319 35 (:DEFINITION ACK-DEFAULT))
 (189 9 (:REWRITE O<=-O-FINP-DEF))
 (152 19 (:REWRITE UNICITY-OF-0))
 (150 150 (:TYPE-PRESCRIPTION O-FINP))
 (150 50 (:REWRITE O-FIRST-EXPT-O-INFP))
 (145 71 (:REWRITE DEFAULT-<-2))
 (128 58 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (123 71 (:REWRITE DEFAULT-<-1))
 (100 100 (:TYPE-PRESCRIPTION BOOLEANP))
 (95 19 (:REWRITE DEFUNG::NATP-FIX))
 (57 19 (:DEFINITION NATP))
 (38 19 (:DEFINITION FIX))
 (37 9 (:REWRITE AC-<))
 (36 4 (:REWRITE O-FIRST-EXPT-<))
 (32 32 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (20 4 (:REWRITE O-FIRST-COEFF-<))
 (19 19 (:TYPE-PRESCRIPTION NATP))
 (18 9 (:REWRITE O-INFP-O-FINP-O<=))
 (9 9 (:REWRITE |a < b & b < c  =>  a < c|))
 )
(ACK-INDUCTION-REDUCTION
 (393 15 (:DEFINITION ACK-DEFINITION))
 (217 123 (:REWRITE DEFAULT-+-2))
 (123 123 (:REWRITE DEFAULT-+-1))
 (122 31 (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
 (94 94 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (86 31 (:REWRITE O-INFP->NEQ-0))
 (33 33 (:TYPE-PRESCRIPTION O-FINP))
 (33 11 (:REWRITE O-FIRST-EXPT-O-INFP))
 (27 27 (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
 (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
 (22 11 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 )
