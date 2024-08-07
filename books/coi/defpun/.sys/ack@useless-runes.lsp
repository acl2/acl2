(NATURAL-LISTP)
(TRUE-LISTP-FROM-NATURAL-LISTP
 (8 8 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 2 (:DEFINITION TRUE-LISTP))
 )
(ACKBASE_BODY_1)
(ACKTEST_BODY_1)
(ACKTEST_BODY_1_TYPE)
(ACKSTEP_BODY_1)
(ACKBASE_BODY)
(ACKTEST_BODY)
(ACKSTEP_BODY)
(|ACK_1_MINTERM-pun-stn|)
(|ACK_1_MINTERM-pun-fch-prop|)
(ACK_1_MINTERM_TERM
 (3 3 (:TYPE-PRESCRIPTION |ACK_1_MINTERM-pun-stn|))
 )
(ACK_1_MINTERM_TERM_TYPE)
(|ACK_1_MINTERM-xtesq|)
(|ACK_1_MINTERM-xbasq|)
(|ACK_1_MINTERM-xsteq|)
(|ACK_1_MINTERM-xun-stn|)
(|ACK_1_MINTERM-xun-fch-fn|)
(|ACK_1_MINTERM-xun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|ACK_1_MINTERM-xun|
 (1 1 (:TYPE-PRESCRIPTION |ACK_1_MINTERM-xun-stn|))
 )
(|ACK_1_MINTERM_pun|)
(ACK_1_MINTERM)
(|ACK_1_MINTERM_ACK_1_MINTERM_pun_reduction|
 (102 96 (:REWRITE DEFAULT-CAR))
 (101 38 (:REWRITE ZP-OPEN))
 (91 91 (:REWRITE DEFAULT-+-2))
 (91 91 (:REWRITE DEFAULT-+-1))
 (69 69 (:REWRITE DEFAULT-CDR))
 (66 22 (:REWRITE FOLD-CONSTS-IN-+))
 (47 45 (:REWRITE DEFAULT-<-1))
 (45 45 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE CAR-CONS))
 (28 28 (:REWRITE CDR-CONS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(|ACK_1_MINTERM_pun_def|)
(ACK_1_MINTERM_PROP
 (14 2 (:DEFINITION |ACK_1_MINTERM-pun-stn|))
 (8 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE |ACK_1_MINTERM-pun-fch-prop|))
 (2 2 (:DEFINITION NOT))
 )
(OPEN-ACK_1_MINTERM)
(NATP_ACK_1_MINTERM)
(ACK_1_MINTERM_TERM_PROP)
(ACK_1_MEASURE)
(ACK_1_TERMINATES)
(ACK_1_TERMINATES_TYPE)
(OPEN_ACK_1_MEASURE
 (23 23 (:REWRITE DEFAULT-CDR))
 (23 23 (:REWRITE DEFAULT-CAR))
 (16 15 (:REWRITE DEFAULT-<-1))
 (16 12 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-<-2))
 (14 12 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_1_TERMINATES)
(ACK_MEASURE)
(ACK_TERMINATES)
(ACK_TERMINATES_TYPE)
(OPEN_ACK_MEASURE
 (54 6 (:REWRITE OPEN_ACK_1_TERMINATES))
 (40 40 (:REWRITE DEFAULT-CDR))
 (40 40 (:REWRITE DEFAULT-CAR))
 (28 22 (:REWRITE DEFAULT-+-2))
 (26 22 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_MEASURE!)
(OPEN_ACK_TERMINATES
 (76 76 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (63 56 (:REWRITE DEFAULT-+-2))
 (63 56 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_TERMINATES_X
 (76 76 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (63 56 (:REWRITE DEFAULT-+-2))
 (63 56 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_TERMINATES_Y
 (76 76 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (63 56 (:REWRITE DEFAULT-+-2))
 (63 56 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_TERMINATES_XARGS
 (76 76 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (63 56 (:REWRITE DEFAULT-+-2))
 (63 56 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_TERMINATES!
 (76 76 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (63 56 (:REWRITE DEFAULT-+-2))
 (63 56 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ACK_EXECUTION
 (211 211 (:REWRITE DEFAULT-CDR))
 (211 211 (:REWRITE DEFAULT-CAR))
 (84 77 (:REWRITE DEFAULT-+-2))
 (78 77 (:REWRITE DEFAULT-+-1))
 (16 13 (:REWRITE DEFAULT-<-2))
 (16 13 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ACK_EXECUTION_NON_TERMINATING
 (72 4 (:REWRITE OPEN_ACK_TERMINATES))
 (64 4 (:DEFINITION ACKTEST_BODY))
 (60 4 (:DEFINITION ACKTEST_BODY_1))
 (19 19 (:TYPE-PRESCRIPTION ACK_EXECUTION))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE CDR-CONS))
 (12 12 (:REWRITE CAR-CONS))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:TYPE-PRESCRIPTION ACKTEST_BODY))
 (4 4 (:REWRITE ZP-OPEN))
 )
(ACK_EXECUTION
 (642 642 (:TYPE-PRESCRIPTION ACK_EXECUTION))
 (477 24 (:DEFINITION ACK_EXECUTION))
 (182 182 (:REWRITE DEFAULT-+-2))
 (182 182 (:REWRITE DEFAULT-+-1))
 (148 64 (:REWRITE ZP-OPEN))
 (134 134 (:REWRITE DEFAULT-CAR))
 (132 132 (:REWRITE DEFAULT-CDR))
 (124 36 (:REWRITE FOLD-CONSTS-IN-+))
 (91 91 (:REWRITE DEFAULT-<-2))
 (91 91 (:REWRITE DEFAULT-<-1))
 (16 8 (:REWRITE UNICITY-OF-0))
 (8 8 (:DEFINITION FIX))
 )
(ACK
 (211 211 (:REWRITE DEFAULT-CDR))
 (211 211 (:REWRITE DEFAULT-CAR))
 (84 77 (:REWRITE DEFAULT-+-2))
 (78 77 (:REWRITE DEFAULT-+-1))
 (16 13 (:REWRITE DEFAULT-<-2))
 (16 13 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(OPEN_ACK_REC_TERM
 (230 200 (:REWRITE DEFAULT-+-2))
 (214 200 (:REWRITE DEFAULT-+-1))
 (211 211 (:REWRITE DEFAULT-CDR))
 (211 211 (:REWRITE DEFAULT-CAR))
 (124 52 (:REWRITE ZP-OPEN))
 (121 28 (:REWRITE FOLD-CONSTS-IN-+))
 (50 50 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (24 9 (:REWRITE UNICITY-OF-0))
 (15 9 (:DEFINITION FIX))
 )
(ACK_EXECUTION_TO_ACK
 (366 366 (:REWRITE DEFAULT-CDR))
 (366 366 (:REWRITE DEFAULT-CAR))
 (277 277 (:TYPE-PRESCRIPTION ACK_EXECUTION))
 (241 17 (:REWRITE ACK_EXECUTION_NON_TERMINATING))
 (170 139 (:REWRITE DEFAULT-+-2))
 (170 139 (:REWRITE DEFAULT-+-1))
 (62 62 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (49 40 (:REWRITE ZP-OPEN))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(ACK
 (159 159 (:REWRITE DEFAULT-+-2))
 (159 159 (:REWRITE DEFAULT-+-1))
 (123 33 (:REWRITE FOLD-CONSTS-IN-+))
 (87 33 (:REWRITE ZP-OPEN))
 (45 45 (:REWRITE DEFAULT-<-2))
 (45 45 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE UNICITY-OF-0))
 (22 22 (:REWRITE DEFAULT-CDR))
 (12 12 (:DEFINITION FIX))
 )
(ACK_INDUCTION
 (211 211 (:REWRITE DEFAULT-CDR))
 (211 211 (:REWRITE DEFAULT-CAR))
 (84 77 (:REWRITE DEFAULT-+-2))
 (78 77 (:REWRITE DEFAULT-+-1))
 (16 13 (:REWRITE DEFAULT-<-2))
 (16 13 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(HEAD-EQUAL)
(LIST-EQUAL)
(OPEN-LIST-EQUAL
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(LIST-EQUAL-IS-AN-EQUIVALENCE
 (222 222 (:REWRITE DEFAULT-CAR))
 (132 132 (:REWRITE DEFAULT-CDR))
 )
(LIST-EQUAL-IMPLIES-EQUAL-CONSP-1
 (4 4 (:REWRITE OPEN-LIST-EQUAL))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(LIST-EQUAL-IMPLIES-LIST-EQUAL-CONS-2
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(LIST-EQUAL-IMPLIES-EQUAL-CAR-1
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE OPEN-LIST-EQUAL))
 )
(LIST-EQUAL-IMPLIES-LIST-EQUAL-CDR-1
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE OPEN-LIST-EQUAL))
 )
(CDR-APPEND-CONSP
 (78 39 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (39 39 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (39 39 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (9 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(CAR-APPEND-CONSP
 (53 53 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (30 9 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(LEN-APPEND
 (48 24 (:REWRITE DEFAULT-+-2))
 (31 24 (:REWRITE DEFAULT-+-1))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (18 15 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (4 4 (:REWRITE CDR-APPEND-CONSP))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(LEN-CONS
 (10 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(APPEND-CONSP-TYPE-TWO
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(APPEND-OF-CONS
 (44 22 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (22 22 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (22 22 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(APPEND-OF-NON-CONSP-ONE
 (38 19 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (19 19 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (19 19 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (19 19 (:TYPE-PRESCRIPTION APPEND-CONSP-TYPE-TWO))
 )
(LIST-EQUAL-IMPLICATION
 (16 8 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 5 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE OPEN-LIST-EQUAL))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(NOT-CONSP-IMPLICATION
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(HEAD-EQUAL-APPEND
 (104 52 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (52 52 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (52 52 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (52 52 (:TYPE-PRESCRIPTION APPEND-CONSP-TYPE-TWO))
 (35 23 (:REWRITE DEFAULT-CAR))
 (14 10 (:REWRITE DEFAULT-CDR))
 (14 2 (:REWRITE CDR-APPEND-CONSP))
 (4 2 (:REWRITE CAR-APPEND-CONSP))
 )
(ACK_TERMINATES_FROM_ACK_TERMINATES
 (288 288 (:REWRITE DEFAULT-CDR))
 (244 244 (:REWRITE DEFAULT-CAR))
 (162 104 (:REWRITE DEFAULT-+-2))
 (120 104 (:REWRITE DEFAULT-+-1))
 (34 34 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (29 29 (:REWRITE NOT-CONSP-IMPLICATION))
 (24 12 (:REWRITE DEFAULT-<-1))
 (19 12 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE ZP-OPEN))
 )
(ACK_TERMINATES_LIST_EQUAL
 (36 2 (:REWRITE OPEN_ACK_TERMINATES))
 (32 2 (:DEFINITION ACKTEST_BODY))
 (30 2 (:DEFINITION ACKTEST_BODY_1))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION ACKTEST_BODY))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE OPEN-LIST-EQUAL))
 )
(NOT_ACK_TERMINATES_LIST_EQUAL)
(LIST-EQUAL-IMPLIES-IFF-ACK_TERMINATES-3
 (36 2 (:REWRITE OPEN_ACK_TERMINATES))
 (32 2 (:DEFINITION ACKTEST_BODY))
 (30 2 (:DEFINITION ACKTEST_BODY_1))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION ACKTEST_BODY))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE OPEN-LIST-EQUAL))
 (1 1 (:REWRITE ACK_TERMINATES_FROM_ACK_TERMINATES))
 )
(ACK_TERMINATES_NIL
 (36 2 (:REWRITE OPEN_ACK_TERMINATES))
 (32 2 (:DEFINITION ACKTEST_BODY))
 (30 2 (:DEFINITION ACKTEST_BODY_1))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (5 1 (:DEFINITION LEN))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION ACKTEST_BODY))
 (2 2 (:REWRITE ZP-OPEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LIST-EQUAL-IMPLIES-EQUAL-ACK-3
 (389 43 (:REWRITE ACK_TERMINATES_FROM_ACK_TERMINATES))
 (330 330 (:REWRITE DEFAULT-CDR))
 (324 324 (:REWRITE DEFAULT-CAR))
 (295 239 (:REWRITE DEFAULT-+-2))
 (290 30 (:DEFINITION HEAD-EQUAL))
 (265 239 (:REWRITE DEFAULT-+-1))
 (185 40 (:REWRITE FOLD-CONSTS-IN-+))
 (157 49 (:REWRITE ZP-OPEN))
 (94 94 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (58 58 (:REWRITE NOT-CONSP-IMPLICATION))
 (38 13 (:REWRITE UNICITY-OF-0))
 (36 36 (:REWRITE DEFAULT-<-2))
 (36 36 (:REWRITE DEFAULT-<-1))
 (25 13 (:DEFINITION FIX))
 )
(OPEN_ACK_TERMINATES-1
 (106 106 (:REWRITE DEFAULT-CDR))
 (106 106 (:REWRITE DEFAULT-CAR))
 (81 72 (:REWRITE DEFAULT-+-2))
 (81 72 (:REWRITE DEFAULT-+-1))
 (33 9 (:REWRITE ACK_TERMINATES_FROM_ACK_TERMINATES))
 (29 29 (:REWRITE ZP-OPEN))
 (18 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 2 (:DEFINITION HEAD-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION HEAD-EQUAL))
 (4 4 (:REWRITE NOT-CONSP-IMPLICATION))
 )
(ACK_TERMIANTES_ON_ACK
 (320 308 (:REWRITE DEFAULT-CDR))
 (291 279 (:REWRITE DEFAULT-CAR))
 (186 116 (:REWRITE DEFAULT-+-2))
 (142 116 (:REWRITE DEFAULT-+-1))
 (96 48 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (83 29 (:REWRITE NOT-CONSP-IMPLICATION))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (38 38 (:REWRITE OPEN_ACK_TERMINATES))
 (28 28 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE ZP-OPEN))
 )
(ACK_MEASURE_ON_ACK
 (3854 3353 (:REWRITE DEFAULT-CDR))
 (3583 3082 (:REWRITE DEFAULT-CAR))
 (1404 702 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1119 36 (:REWRITE ACK_TERMIANTES_ON_ACK))
 (702 702 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (646 316 (:REWRITE OPEN_ACK_TERMINATES))
 (407 158 (:REWRITE NOT-CONSP-IMPLICATION))
 (130 129 (:REWRITE DEFAULT-<-2))
 (129 129 (:REWRITE DEFAULT-<-1))
 (116 116 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ACK_MEASURE_REDUCTION
 (33 2 (:REWRITE ACK_TERMINATES_FROM_ACK_TERMINATES))
 (24 3 (:DEFINITION HEAD-EQUAL))
 (20 1 (:DEFINITION ACK))
 (9 9 (:TYPE-PRESCRIPTION HEAD-EQUAL))
 (8 6 (:REWRITE DEFAULT-+-2))
 (8 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE NOT-CONSP-IMPLICATION))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE OPEN_ACK_TERMINATES))
 )
(ACK_ON_ACK
 (625 508 (:REWRITE DEFAULT-CDR))
 (591 474 (:REWRITE DEFAULT-CAR))
 (512 366 (:REWRITE DEFAULT-+-2))
 (484 242 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (430 366 (:REWRITE DEFAULT-+-1))
 (333 81 (:REWRITE NOT-CONSP-IMPLICATION))
 (242 242 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (105 105 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (80 80 (:REWRITE OPEN_ACK_TERMINATES))
 (56 56 (:REWRITE DEFAULT-<-2))
 (56 56 (:REWRITE DEFAULT-<-1))
 (38 13 (:REWRITE UNICITY-OF-0))
 (25 13 (:DEFINITION FIX))
 )
(ACK_REDUCTION
 (100 3 (:DEFINITION ACK))
 (35 4 (:REWRITE ACK_TERMINATES_FROM_ACK_TERMINATES))
 (27 22 (:REWRITE DEFAULT-+-2))
 (27 22 (:REWRITE DEFAULT-+-1))
 (24 3 (:DEFINITION HEAD-EQUAL))
 (20 5 (:REWRITE COMMUTATIVITY-OF-+))
 (18 8 (:REWRITE ZP-OPEN))
 (9 9 (:TYPE-PRESCRIPTION HEAD-EQUAL))
 (6 6 (:REWRITE OPEN_ACK_TERMINATES))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE NOT-CONSP-IMPLICATION))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(AK)
(AK_TERMINATES)
(AK_MEASURE)
(AK_SPEC
 (136 120 (:REWRITE DEFAULT-+-2))
 (134 120 (:REWRITE DEFAULT-+-1))
 (119 119 (:REWRITE DEFAULT-CDR))
 (87 34 (:REWRITE ZP-OPEN))
 (83 83 (:REWRITE DEFAULT-CAR))
 (50 16 (:REWRITE FOLD-CONSTS-IN-+))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE NOT-CONSP-IMPLICATION))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:DEFINITION FIX))
 )
(AK_MEASURE_SPEC
 (196 196 (:REWRITE DEFAULT-CDR))
 (136 136 (:REWRITE DEFAULT-CAR))
 (128 102 (:REWRITE DEFAULT-+-2))
 (109 102 (:REWRITE DEFAULT-+-1))
 (67 3 (:DEFINITION ACK))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:DEFINITION FIX))
 )
