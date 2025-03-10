(GL::G-LOGAPP-OF-INTEGERS)
(GL::DEPENDS-ON-OF-APPEND
 (80 80 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (55 13 (:REWRITE DEFAULT-CDR))
 (31 22 (:REWRITE DEFAULT-CAR))
 (30 6 (:REWRITE CONSP-OF-APPEND))
 (28 14 (:REWRITE GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (21 3 (:REWRITE CAR-OF-APPEND))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 )
(GL::DEPENDS-ON-OF-REV
 (88 88 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (75 3 (:DEFINITION BINARY-APPEND))
 (48 48 (:TYPE-PRESCRIPTION REV))
 (47 17 (:REWRITE DEFAULT-CAR))
 (42 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (41 11 (:REWRITE DEFAULT-CDR))
 (39 21 (:REWRITE CONSP-OF-REV))
 (23 10 (:REWRITE GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP))
 (20 5 (:REWRITE GL::PBFR-DEPENDS-ON-CDR))
 (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::DEPS-OF-G-LOGAPP-OF-INTEGERS
 (369 3 (:DEFINITION GL::GOBJ-DEPENDS-ON))
 (159 3 (:REWRITE GL::GENERAL-INTEGERP-WHEN-GENERAL-CONCRETEP))
 (147 3 (:DEFINITION GL::GENERAL-CONCRETEP-DEF))
 (108 36 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (75 75 (:TYPE-PRESCRIPTION BOOLEANP))
 (44 43 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-ATOM))
 (43 43 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-VAR))
 (43 43 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-CONCRETE))
 (36 36 (:REWRITE GL::TAG-WHEN-ATOM))
 (36 36 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (36 36 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (24 24 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP))
 (21 3 (:REWRITE GL::GOBJ-LIST-DEPENDS-ON-OF-G-APPLY->ARGS))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->THEN))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->TEST))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-ITE->ELSE))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-INTEGER->BITS))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-OF-G-BOOLEAN->BOOL))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-CDR-OF-GOBJ))
 (21 3 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ))
 (15 3 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ-LIST))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (9 9 (:TYPE-PRESCRIPTION GL::GOBJ-LIST-DEPENDS-ON))
 (9 9 (:REWRITE GL::GENERAL-CONCRETEP-OF-ATOMIC-CONSTANTS))
 (6 6 (:REWRITE GL::GOBJ-LIST-DEPENDS-ON-OF-ATOM))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP))
 (6 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (3 3 (:TYPE-PRESCRIPTION GL::GENERAL-INTEGER-BITS))
 (3 3 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (3 3 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOM))
 (1 1 (:TYPE-PRESCRIPTION MK-G-INTEGER))
 )
(GL::LOGAPP-ZP-N
 (4 1 (:REWRITE ZP-WHEN-GT-0))
 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (2 2 (:REWRITE IFIX-WHEN-INTEGERP))
 (1 1 (:REWRITE ZP-WHEN-INTEGERP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(GL::LOGAPP-ZIP-X
 (23 2 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (12 1 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (10 2 (:REWRITE NFIX-WHEN-NATP))
 (7 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (5 2 (:REWRITE ZP-WHEN-GT-0))
 (5 2 (:REWRITE NATP-WHEN-GTE-0))
 (5 2 (:REWRITE ASH-0))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE ZP-WHEN-INTEGERP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE GL::LOGAPP-ZP-N))
 (2 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (2 1 (:REWRITE IFIX-WHEN-INTEGERP))
 (1 1 (:TYPE-PRESCRIPTION IFIX))
 (1 1 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 )
(GL::LOGAPP-ZIP-Y
 (35 2 (:REWRITE LOGHEAD-IDENTITY))
 (31 1 (:DEFINITION UNSIGNED-BYTE-P))
 (25 1 (:DEFINITION INTEGER-RANGE-P))
 (7 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:LINEAR EXPT->-1))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (2 1 (:REWRITE GL::LOGAPP-ZP-N))
 (2 1 (:REWRITE GL::LOGAPP-ZIP-X))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(GL::BFR-LIST->S-WHEN-GTE-0
 (1728 80 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (1452 80 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (1012 84 (:DEFINITION TRUE-LISTP))
 (1008 168 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (648 648 (:TYPE-PRESCRIPTION LEN))
 (496 84 (:DEFINITION LEN))
 (442 442 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (413 323 (:REWRITE DEFAULT-CDR))
 (408 408 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (336 336 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (336 168 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (215 95 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (176 88 (:REWRITE DEFAULT-+-2))
 (174 87 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (168 168 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (168 168 (:REWRITE SET::IN-SET))
 (159 62 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (142 71 (:REWRITE GL::BFR-EVAL-BOOLEANP))
 (132 80 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (118 58 (:REWRITE DEFAULT-CAR))
 (103 103 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (97 97 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (97 97 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (91 91 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (88 88 (:REWRITE DEFAULT-+-1))
 (82 41 (:REWRITE GL::SCDR-WHEN-S-ENDP))
 (76 76 (:LINEAR INDEX-OF-<-LEN))
 (71 71 (:TYPE-PRESCRIPTION BOOLEANP))
 (46 46 (:TYPE-PRESCRIPTION POSP))
 (35 35 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (22 13 (:REWRITE DEFAULT-<-1))
 (22 2 (:REWRITE BFIX-WHEN-NOT-1))
 (18 18 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (15 15 (:META CANCEL_PLUS-LESSP-CORRECT))
 (13 13 (:REWRITE DEFAULT-<-2))
 (8 2 (:REWRITE EQUAL-1-OF-BOOL->BIT))
 (6 6 (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT))
 (6 4 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (4 2 (:REWRITE BFIX-WHEN-NOT-BITP))
 (4 2 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (4 2 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 )
(GL::G-LOGAPP-OF-INTEGERS-CORRECT
 (1617 27 (:DEFINITION GL::GENERAL-CONCRETEP-DEF))
 (836 38 (:REWRITE GL::GENERAL-CONCRETE-OBJ-WHEN-NUMBERP))
 (720 9 (:REWRITE GL::GENERAL-INTEGERP-WHEN-GENERAL-CONCRETEP))
 (384 162 (:REWRITE GL::POSSIBILITIES-FOR-X-9))
 (378 378 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP))
 (338 112 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (258 4 (:REWRITE GL::GENERAL-CONCRETE-OBJ-CORRECT-FOR-EVAL-G-BASE))
 (230 230 (:TYPE-PRESCRIPTION BOOLEANP))
 (162 162 (:REWRITE GL::TAG-WHEN-ATOM))
 (145 81 (:REWRITE GL::POSSIBILITIES-FOR-X-10))
 (114 38 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (112 112 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (112 112 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (82 81 (:REWRITE GL::POSSIBILITIES-FOR-X-2))
 (81 81 (:REWRITE GL::GENERAL-CONCRETEP-OF-ATOMIC-CONSTANTS))
 (78 78 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (66 6 (:DEFINITION GL::BFR-LIST->U))
 (59 49 (:REWRITE DEFAULT-CAR))
 (43 20 (:REWRITE DEFAULT-<-1))
 (38 38 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (33 33 (:REWRITE DEFAULT-CDR))
 (24 8 (:REWRITE GL::LOGAPP-ZIP-Y))
 (24 8 (:REWRITE GL::LOGAPP-ZIP-X))
 (24 2 (:REWRITE BITOPS::LOGAPP-SIGN))
 (22 22 (:META CANCEL_PLUS-LESSP-CORRECT))
 (20 20 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION ZIP))
 (16 8 (:REWRITE GL::BFR-EVAL-BOOLEANP))
 (9 9 (:REWRITE GL::POSSIBILITIES-FOR-X-8))
 (9 9 (:REWRITE GL::POSSIBILITIES-FOR-X-7))
 (9 9 (:REWRITE GL::POSSIBILITIES-FOR-X-6))
 (9 9 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (9 9 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOM))
 (7 7 (:TYPE-PRESCRIPTION ZP))
 (6 6 (:TYPE-PRESCRIPTION GL::BFR-LIST->U-TYPE))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (6 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION MK-G-INTEGER))
 (3 3 (:REWRITE GL::GENERAL-CONSP-CORRECT-FOR-EVAL-G-BASE))
 )
(GL-SYM::|ACL2::LOGAPP$|
 (2883 51 (:DEFINITION ACL2-COUNT))
 (1234 399 (:REWRITE DEFAULT-+-2))
 (783 399 (:REWRITE DEFAULT-+-1))
 (390 78 (:DEFINITION INTEGER-ABS))
 (390 39 (:DEFINITION LENGTH))
 (273 39 (:DEFINITION LEN))
 (168 168 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (144 48 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (116 116 (:REWRITE FOLD-CONSTS-IN-+))
 (108 6 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (102 102 (:REWRITE DEFAULT-CDR))
 (96 96 (:TYPE-PRESCRIPTION BOOLEANP))
 (82 82 (:REWRITE DEFAULT-<-2))
 (82 82 (:REWRITE DEFAULT-<-1))
 (78 78 (:REWRITE DEFAULT-UNARY-MINUS))
 (78 6 (:DEFINITION MEMBER-EQUAL))
 (72 72 (:REWRITE GL::TAG-WHEN-ATOM))
 (63 63 (:REWRITE DEFAULT-CAR))
 (48 48 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (48 48 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (39 39 (:TYPE-PRESCRIPTION LEN))
 (39 39 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (39 39 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (39 39 (:REWRITE DEFAULT-REALPART))
 (39 39 (:REWRITE DEFAULT-NUMERATOR))
 (39 39 (:REWRITE DEFAULT-IMAGPART))
 (39 39 (:REWRITE DEFAULT-DENOMINATOR))
 (39 39 (:REWRITE DEFAULT-COERCE-2))
 (39 39 (:REWRITE DEFAULT-COERCE-1))
 (24 24 (:REWRITE GL::GENERAL-CONCRETEP-OF-ATOMIC-CONSTANTS))
 (16 4 (:REWRITE ZP-WHEN-GT-0))
 (12 12 (:REWRITE SUBSETP-MEMBER . 2))
 (12 12 (:REWRITE SUBSETP-MEMBER . 1))
 (6 3 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (6 3 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-CONSP))
 (6 3 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-BOOLEANP))
 (4 4 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:TYPE-PRESCRIPTION GL::GENERAL-CONSP))
 (3 3 (:TYPE-PRESCRIPTION GL::GENERAL-BOOLEANP))
 )
(GL-SYM::|ACL2::LOGAPP$-PRESERVES-HYP|
 (3759 1253 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2506 2506 (:TYPE-PRESCRIPTION BOOLEANP))
 (1253 1253 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1253 1253 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (972 108 (:REWRITE GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (710 710 (:TYPE-PRESCRIPTION GL::BFR-HYP-FIX))
 (699 699 (:REWRITE SUBSETP-MEMBER . 4))
 (699 699 (:REWRITE SUBSETP-MEMBER . 3))
 (699 699 (:REWRITE SUBSETP-MEMBER . 2))
 (699 699 (:REWRITE SUBSETP-MEMBER . 1))
 (699 699 (:REWRITE INTERSECTP-MEMBER . 3))
 (699 699 (:REWRITE INTERSECTP-MEMBER . 2))
 (546 273 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (546 273 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-CONSP))
 (546 273 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-BOOLEANP))
 (543 543 (:REWRITE GL::GENERAL-CONCRETEP-OF-ATOMIC-CONSTANTS))
 (452 226 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (364 364 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (273 273 (:TYPE-PRESCRIPTION GL::GENERAL-CONSP))
 (273 273 (:TYPE-PRESCRIPTION GL::GENERAL-BOOLEANP))
 (226 226 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (170 170 (:REWRITE DEFAULT-CDR))
 (170 170 (:REWRITE DEFAULT-CAR))
 (160 40 (:REWRITE ZP-WHEN-GT-0))
 (156 21 (:REWRITE GL::LOGAPP-ZP-N))
 (156 21 (:REWRITE GL::LOGAPP-ZIP-Y))
 (156 21 (:REWRITE GL::LOGAPP-ZIP-X))
 (118 118 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (42 42 (:TYPE-PRESCRIPTION ZIP))
 (40 40 (:REWRITE ZP-WHEN-INTEGERP))
 (40 40 (:REWRITE ZP-OPEN))
 (40 40 (:REWRITE DEFAULT-<-2))
 (40 40 (:REWRITE DEFAULT-<-1))
 (40 40 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(GL-SYM::|ACL2::LOGAPP$-OF-BFR-HYP-FIX|
 (6775 2261 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (4506 4506 (:TYPE-PRESCRIPTION BOOLEANP))
 (2261 2261 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2261 2261 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1944 216 (:REWRITE GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (1642 821 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (1317 1317 (:REWRITE SUBSETP-MEMBER . 4))
 (1317 1317 (:REWRITE SUBSETP-MEMBER . 3))
 (1317 1317 (:REWRITE SUBSETP-MEMBER . 2))
 (1317 1317 (:REWRITE SUBSETP-MEMBER . 1))
 (1317 1317 (:REWRITE INTERSECTP-MEMBER . 3))
 (1317 1317 (:REWRITE INTERSECTP-MEMBER . 2))
 (1092 546 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (1092 546 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-CONSP))
 (1092 546 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-BOOLEANP))
 (1018 1018 (:REWRITE GL::GENERAL-CONCRETEP-OF-ATOMIC-CONSTANTS))
 (821 821 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (686 686 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (546 546 (:TYPE-PRESCRIPTION GL::GENERAL-CONSP))
 (546 546 (:TYPE-PRESCRIPTION GL::GENERAL-BOOLEANP))
 (351 335 (:REWRITE DEFAULT-CDR))
 (351 335 (:REWRITE DEFAULT-CAR))
 (312 42 (:REWRITE GL::LOGAPP-ZP-N))
 (312 42 (:REWRITE GL::LOGAPP-ZIP-Y))
 (312 42 (:REWRITE GL::LOGAPP-ZIP-X))
 (304 76 (:REWRITE ZP-WHEN-GT-0))
 (236 236 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (84 84 (:TYPE-PRESCRIPTION ZIP))
 (76 76 (:REWRITE ZP-WHEN-INTEGERP))
 (76 76 (:REWRITE ZP-OPEN))
 (76 76 (:REWRITE DEFAULT-<-2))
 (76 76 (:REWRITE DEFAULT-<-1))
 (76 76 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(GL::|BFR-HYP-EQUIV-IMPLIES-EQUAL-ACL2::LOGAPP$-4|)
(GL-SYM::|ACL2::LOGAPP$|
 (4584 4584 (:TYPE-PRESCRIPTION GL::BFR-UNASSUME$A))
 (652 652 (:TYPE-PRESCRIPTION BOOLEANP))
 (398 62 (:REWRITE GL::GLCP-CONFIG-P-WHEN-WRONG-TAG))
 (361 361 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (361 361 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (336 112 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (271 271 (:REWRITE GL::TAG-WHEN-ATOM))
 (165 165 (:TYPE-PRESCRIPTION GL::BFR-UNASSUME))
 (115 115 (:TYPE-PRESCRIPTION GL::BFR-HYP-FIX))
 (112 56 (:REWRITE GL::TAG-WHEN-GLCP-CONFIG-P))
 (108 108 (:REWRITE GL::BFR-ASSUME-CORRECT))
 (96 96 (:TYPE-PRESCRIPTION MK-G-ITE))
 (96 48 (:TYPE-PRESCRIPTION GL::MK-G-BDD-ITE))
 (74 74 (:REWRITE DEFAULT-<-2))
 (74 74 (:REWRITE DEFAULT-<-1))
 (74 74 (:META CANCEL_PLUS-LESSP-CORRECT))
 (72 72 (:REWRITE SUBSETP-MEMBER . 4))
 (72 72 (:REWRITE SUBSETP-MEMBER . 3))
 (72 72 (:REWRITE SUBSETP-MEMBER . 2))
 (72 72 (:REWRITE SUBSETP-MEMBER . 1))
 (72 72 (:REWRITE INTERSECTP-MEMBER . 3))
 (72 72 (:REWRITE INTERSECTP-MEMBER . 2))
 (56 56 (:REWRITE NATP-RW))
 (36 36 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (32 8 (:REWRITE ZP-WHEN-GT-0))
 (32 2 (:REWRITE DEFAULT-CDR))
 (32 2 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE NATP-WHEN-INTEGERP))
 (24 21 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOM))
 (21 21 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (16 2 (:REWRITE GL::LOGAPP-ZP-N))
 (16 2 (:REWRITE GL::LOGAPP-ZIP-Y))
 (16 2 (:REWRITE GL::LOGAPP-ZIP-X))
 (12 6 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (12 6 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-CONSP))
 (12 6 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-BOOLEANP))
 (6 6 (:TYPE-PRESCRIPTION GL::GENERAL-CONSP))
 (6 6 (:TYPE-PRESCRIPTION GL::GENERAL-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION ZIP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 )
(GL-THM::LOGAPP-DEPENDENCIES
 (10164 3388 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (7089 7089 (:TYPE-PRESCRIPTION BOOLEANP))
 (3388 3388 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3388 3388 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3263 3263 (:REWRITE GL::GOBJ-DEPENDS-ON-WHEN-G-CONCRETE))
 (3230 1615 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (3230 1615 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-CONSP))
 (3230 1615 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-BOOLEANP))
 (1565 313 (:REWRITE GL::GOBJ-DEPENDS-ON-CAR-OF-GOBJ-LIST))
 (1551 1551 (:TYPE-PRESCRIPTION GL::GENERAL-CONSP))
 (1551 1551 (:TYPE-PRESCRIPTION GL::GENERAL-BOOLEANP))
 (1392 1392 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (792 88 (:REWRITE GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (672 672 (:REWRITE DEFAULT-CDR))
 (672 672 (:REWRITE DEFAULT-CAR))
 (626 313 (:REWRITE GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP))
 (321 321 (:REWRITE SUBSETP-MEMBER . 4))
 (321 321 (:REWRITE SUBSETP-MEMBER . 3))
 (321 321 (:REWRITE SUBSETP-MEMBER . 2))
 (321 321 (:REWRITE SUBSETP-MEMBER . 1))
 (321 321 (:REWRITE INTERSECTP-MEMBER . 3))
 (321 321 (:REWRITE INTERSECTP-MEMBER . 2))
 (204 204 (:TYPE-PRESCRIPTION GL::GL-CONS))
 (146 146 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (126 63 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (63 63 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (44 7 (:REWRITE GL::LOGAPP-ZP-N))
 (44 7 (:REWRITE GL::LOGAPP-ZIP-Y))
 (44 7 (:REWRITE GL::LOGAPP-ZIP-X))
 (16 4 (:REWRITE ZP-WHEN-GT-0))
 (14 14 (:TYPE-PRESCRIPTION ZIP))
 (4 4 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 3 (:TYPE-PRESCRIPTION GL::G-LOGAPP-OF-INTEGERS))
 (1 1 (:TYPE-PRESCRIPTION GL::PBFR-LIST-DEPENDS-ON))
 (1 1 (:TYPE-PRESCRIPTION GL::PBFR-DEPENDS-ON))
 )
(GL::LOGAPP-NON-INTEGERS
 (35 2 (:REWRITE LOGHEAD-IDENTITY))
 (31 1 (:DEFINITION UNSIGNED-BYTE-P))
 (25 1 (:DEFINITION INTEGER-RANGE-P))
 (23 2 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (12 1 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (10 2 (:REWRITE NFIX-WHEN-NATP))
 (9 6 (:REWRITE DEFAULT-<-2))
 (7 7 (:TYPE-PRESCRIPTION ZIP))
 (7 7 (:META CANCEL_PLUS-LESSP-CORRECT))
 (7 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (5 2 (:REWRITE ZP-WHEN-GT-0))
 (5 2 (:REWRITE NATP-WHEN-GTE-0))
 (5 2 (:REWRITE ASH-0))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (4 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (4 3 (:REWRITE IFIX-WHEN-INTEGERP))
 (4 1 (:LINEAR EXPT->-1))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE ZP-WHEN-INTEGERP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 )
(GL-THM::|ACL2::LOGAPP$-CORRECT|
 (16607 15315 (:REWRITE DEFAULT-CAR))
 (15721 5232 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (10810 10810 (:TYPE-PRESCRIPTION BOOLEANP))
 (5816 168 (:DEFINITION GL::BFR-LIST->S))
 (5232 5232 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5232 5232 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4604 448 (:REWRITE GL::BFR-LIST->S-WHEN-GTE-0))
 (3250 1625 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (3250 1625 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-CONSP))
 (3250 1625 (:TYPE-PRESCRIPTION GL::GENERAL-CONCRETEP-NOT-GENERAL-BOOLEANP))
 (2849 2849 (:TYPE-PRESCRIPTION GL::GENERAL-CONSP))
 (2737 2737 (:TYPE-PRESCRIPTION GL::GENERAL-BOOLEANP))
 (2630 2630 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2540 1270 (:REWRITE GL::GENERAL-CONSP-CORRECT-FOR-EVAL-G-BASE))
 (2316 1158 (:REWRITE GL::GENERAL-BOOLEAN-VALUE-CORRECT-FOR-EVAL-G-BASE))
 (1848 168 (:DEFINITION GL::FIRST/REST/END))
 (1799 411 (:REWRITE GL::INTEGERP-OF-GEVAL-FOR-EVAL-G-BASE))
 (1701 1701 (:REWRITE DEFAULT-CDR))
 (1344 1344 (:TYPE-PRESCRIPTION GL::GENERAL-INTEGER-BITS))
 (1344 448 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (1062 118 (:REWRITE GL::GENERAL-CONCRETEP-NOT-GENERAL-INTEGERP))
 (960 396 (:REWRITE GL::BFR-EVAL-BOOLEANP))
 (954 18 (:REWRITE GL::GENERAL-CONCRETE-OBJ-CORRECT))
 (908 168 (:REWRITE GL::GENERAL-CONCRETE-OBJ-WHEN-NUMBERP))
 (816 272 (:REWRITE GL::EVAL-G-BASE-EV-OF-MAYBE-INTEGER-CALL))
 (816 272 (:REWRITE GL::EVAL-G-BASE-EV-OF-INT-SET-SIGN-CALL))
 (816 272 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-MINUS-FOR-GL-CALL))
 (654 291 (:REWRITE GL::LOGAPP-ZIP-X))
 (624 291 (:REWRITE GL::LOGAPP-ZIP-Y))
 (616 616 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (613 613 (:REWRITE GL::GENERAL-INTEGERP-OF-ATOMIC-CONSTANTS))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-ZEROP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-UNARY---CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-TRUNCATE-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-SYMBOLP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-SYMBOL-PACKAGE-NAME-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-SYMBOL-NAME-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-STRINGP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-REM-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-REALPART-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-RATIONALP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-PLUSP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-PKG-WITNESS-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-NUMERATOR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-NULL-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-NOT-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-MOD-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-MINUSP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-LOGNOT-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-LOGBITP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-LISTP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-LAMBDA))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-INTEGERP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-INTEGER-LENGTH-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-IMPLIES-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-IMAGPART-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-IF-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-HONS-ASSOC-EQUAL-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-FLOOR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-EQUAL-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-EQL-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-EQ-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-ENDP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-DENOMINATOR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CONSP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CONS-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-COMPLEX-RATIONALP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-COERCE-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CODE-CHAR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CHARACTERP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CHAR-CODE-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CDR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-CAR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BOOLEANP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BOOL-FIX$INLINE-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BOOL->SIGN-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BOOL->BIT$INLINE-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-LOGXOR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-LOGIOR-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-LOGEQV-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-LOGAND-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-+-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-BINARY-*-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-ATOM-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-ASH-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-ACL2-NUMBERP-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-=-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-<-CALL))
 (612 204 (:REWRITE GL::EVAL-G-BASE-EV-OF-/=-CALL))
 (608 168 (:DEFINITION GL::BOOL->SIGN))
 (585 9 (:REWRITE GL::BFR-ASSUME-OF-GTESTS-POSSIBLY-TRUE))
 (585 9 (:REWRITE GL::BFR-ASSUME-OF-GTESTS-POSSIBLY-FALSE))
 (528 528 (:TYPE-PRESCRIPTION ZIP))
 (504 168 (:REWRITE GL::SCDR-WHEN-S-ENDP))
 (458 264 (:REWRITE DEFAULT-<-1))
 (340 340 (:REWRITE GL::TAG-OF-G-APPLY))
 (324 162 (:REWRITE GL::BFR-HYP-FIX-WHEN-HYP$AP))
 (321 321 (:REWRITE SUBSETP-MEMBER . 4))
 (321 321 (:REWRITE SUBSETP-MEMBER . 3))
 (321 321 (:REWRITE SUBSETP-MEMBER . 2))
 (321 321 (:REWRITE SUBSETP-MEMBER . 1))
 (321 321 (:REWRITE INTERSECTP-MEMBER . 3))
 (321 321 (:REWRITE INTERSECTP-MEMBER . 2))
 (292 12 (:REWRITE LOGHEAD-IDENTITY))
 (291 264 (:REWRITE DEFAULT-<-2))
 (280 280 (:TYPE-PRESCRIPTION GL::TRUE-LISTP-OF-SCDR))
 (272 272 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (270 270 (:META CANCEL_PLUS-LESSP-CORRECT))
 (268 6 (:DEFINITION UNSIGNED-BYTE-P))
 (249 12 (:REWRITE NFIX-WHEN-NATP))
 (237 12 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (193 6 (:DEFINITION INTEGER-RANGE-P))
 (180 12 (:REWRITE NATP-WHEN-INTEGERP))
 (171 6 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (162 162 (:TYPE-PRESCRIPTION GL::HYP$AP))
 (153 12 (:REWRITE NFIX-WHEN-NOT-NATP))
 (137 26 (:REWRITE ZP-WHEN-GT-0))
 (96 12 (:REWRITE ASH-0))
 (78 12 (:REWRITE GL::GTESTS-NONNIL-CORRECT-FOR-EVAL-G-BASE))
 (72 12 (:REWRITE NATP-RW))
 (72 12 (:REWRITE GL::GTESTS-NONNIL-CORRECT))
 (68 68 (:TYPE-PRESCRIPTION GL::G-APPLY))
 (66 12 (:REWRITE NATP-WHEN-GTE-0))
 (66 6 (:REWRITE ZIP-OPEN))
 (62 26 (:REWRITE ZP-WHEN-INTEGERP))
 (60 30 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (48 48 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (45 45 (:REWRITE GL::BOOLEANP-OF-GEVAL-FOR-EVAL-G-BASE))
 (36 18 (:REWRITE GL::GENERIC-GEVAL-WHEN-CONCRETE-GOBJECTP))
 (36 18 (:REWRITE GL::GENERAL-INTEGER-BITS-CORRECT))
 (36 18 (:REWRITE GL::GENERAL-CONSP-CORRECT))
 (36 18 (:REWRITE GL::GENERAL-BOOLEAN-VALUE-CORRECT))
 (36 18 (:REWRITE GL::BOOL-COND-ITEP-EVAL))
 (25 4 (:LINEAR EXPT->-1))
 (24 24 (:TYPE-PRESCRIPTION NFIX))
 (22 22 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (22 22 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (22 22 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (20 20 (:REWRITE ZP-OPEN))
 (18 18 (:TYPE-PRESCRIPTION GL::CONCRETE-GOBJECTP))
 (18 18 (:TYPE-PRESCRIPTION GL::BOOL-COND-ITEP))
 (18 18 (:REWRITE GL::GENERIC-GEVAL-NON-CONS))
 (18 9 (:REWRITE GL::BFR-ASSUME->HYP-CORRECT))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (12 12 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (9 9 (:REWRITE GL::BFR-ASSUME-CORRECT))
 (8 8 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (6 6 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (6 6 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (3 3 (:TYPE-PRESCRIPTION GL::G-LOGAPP-OF-INTEGERS))
 )
