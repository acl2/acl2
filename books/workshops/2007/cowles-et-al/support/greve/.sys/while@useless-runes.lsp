(RUN-SKIP)
(RUN-ASSIGNMENT)
(EVALUATE)
(OP)
(ARG1)
(ARG2)
(ARG3)
(BASE)
(BASE-COMPUTATION)
(RUN-STKBASE_BODY_1)
(RUN-STKTEST_BODY_1)
(RUN-STKSTEP_BODY_1)
(RUN-STKBASE_BODY)
(RUN-STKTEST_BODY)
(RUN-STKSTEP_BODY)
(|RUN-STK_1_MINTERM-pun-stn|)
(|RUN-STK_1_MINTERM-pun-fch-prop|)
(RUN-STK_1_MINTERM_TERM
 (3 3 (:TYPE-PRESCRIPTION |RUN-STK_1_MINTERM-pun-stn|))
 )
(|RUN-STK_1_MINTERM-xtesq|)
(|RUN-STK_1_MINTERM-xbasq|)
(|RUN-STK_1_MINTERM-xsteq|)
(|RUN-STK_1_MINTERM-xun-stn|)
(|RUN-STK_1_MINTERM-xun-fch-fn|)
(|RUN-STK_1_MINTERM-xun-fn|
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(|RUN-STK_1_MINTERM-xun|
 (1 1 (:TYPE-PRESCRIPTION |RUN-STK_1_MINTERM-xun-stn|))
 )
(|RUN-STK_1_MINTERM_pun|)
(RUN-STK_1_MINTERM)
(|RUN-STK_1_MINTERM_RUN-STK_1_MINTERM_pun_reduction|
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
(|RUN-STK_1_MINTERM_pun_def|)
(RUN-STK_1_MINTERM_PROP
 (14 2 (:DEFINITION |RUN-STK_1_MINTERM-pun-stn|))
 (8 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |RUN-STK_1_MINTERM-pun-fch-prop|))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:DEFINITION NOT))
 )
(OPEN-RUN-STK_1_MINTERM)
(NATP_RUN-STK_1_MINTERM)
(RUN-STK_1_MINTERM_TERM_PROP)
(RUN-STK_1_MEASURE)
(RUN-STK_1_TERMINATES)
(OPEN_RUN-STK_1_MEASURE
 (23 23 (:REWRITE DEFAULT-CDR))
 (23 23 (:REWRITE DEFAULT-CAR))
 (4 3 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(OPEN_RUN-STK_1_TERMINATES)
(RUN-STK_MEASURE)
(RUN-STK_TERMINATES)
(OPEN_RUN-STK_MEASURE
 (52 6 (:REWRITE OPEN_RUN-STK_1_TERMINATES))
 (40 40 (:REWRITE DEFAULT-CDR))
 (40 40 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(OPEN_RUN-STK_TERMINATES
 (205 205 (:REWRITE DEFAULT-CDR))
 (205 205 (:REWRITE DEFAULT-CAR))
 )
(OPEN_RUN-STK_TERMINATES_STMT
 (205 205 (:REWRITE DEFAULT-CDR))
 (205 205 (:REWRITE DEFAULT-CAR))
 )
(OPEN_RUN-STK_TERMINATES_MEM
 (205 205 (:REWRITE DEFAULT-CDR))
 (205 205 (:REWRITE DEFAULT-CAR))
 )
(OPEN_RUN-STK_TERMINATES_STK
 (205 205 (:REWRITE DEFAULT-CDR))
 (205 205 (:REWRITE DEFAULT-CAR))
 )
(OPEN_RUN-STK_TERMINATES!
 (205 205 (:REWRITE DEFAULT-CDR))
 (205 205 (:REWRITE DEFAULT-CAR))
 )
(RUN-STK
 (400 400 (:REWRITE DEFAULT-CDR))
 (400 400 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-+-2))
 (18 9 (:REWRITE DEFAULT-<-2))
 (18 9 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(OPEN_RUN-STK_REC_TERM
 (584 584 (:REWRITE DEFAULT-CDR))
 (584 584 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE CONS-CAR-CDR))
 )
(RUN-STK_INDUCTION
 (400 400 (:REWRITE DEFAULT-CDR))
 (400 400 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-+-2))
 (18 9 (:REWRITE DEFAULT-<-2))
 (18 9 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(RUN-STK_TERMINATES_FROM_RUN-STK_TERMINATES
 (1320 1320 (:REWRITE DEFAULT-CDR))
 (1090 1090 (:REWRITE DEFAULT-CAR))
 (424 218 (:REWRITE DEFAULT-+-2))
 (218 218 (:REWRITE DEFAULT-+-1))
 (133 133 (:REWRITE NOT-CONSP-IMPLICATION))
 (116 58 (:REWRITE DEFAULT-<-1))
 (86 58 (:REWRITE DEFAULT-<-2))
 )
(RUN-STK_TERMINATES_LIST_EQUAL
 (34 2 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (30 2 (:DEFINITION RUN-STKTEST_BODY))
 (28 2 (:DEFINITION RUN-STKTEST_BODY_1))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (2 2 (:TYPE-PRESCRIPTION RUN-STKTEST_BODY))
 (2 2 (:DEFINITION BASE))
 (1 1 (:REWRITE OPEN-LIST-EQUAL))
 )
(NOT_RUN-STK_TERMINATES_LIST_EQUAL)
(LIST-EQUAL-IMPLIES-IFF-RUN-STK_TERMINATES-3
 (34 2 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (30 2 (:DEFINITION RUN-STKTEST_BODY))
 (28 2 (:DEFINITION RUN-STKTEST_BODY_1))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (2 2 (:TYPE-PRESCRIPTION RUN-STKTEST_BODY))
 (2 2 (:DEFINITION BASE))
 (1 1 (:REWRITE RUN-STK_TERMINATES_FROM_RUN-STK_TERMINATES))
 (1 1 (:REWRITE OPEN-LIST-EQUAL))
 )
(RUN-STK_TERMINATES_NIL
 (34 2 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (30 2 (:DEFINITION RUN-STKTEST_BODY))
 (28 2 (:DEFINITION RUN-STKTEST_BODY_1))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (5 1 (:DEFINITION LEN))
 (2 2 (:TYPE-PRESCRIPTION RUN-STKTEST_BODY))
 (2 2 (:DEFINITION BASE))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LIST-EQUAL-IMPLIES-EQUAL-RUN-STK-3
 (926 926 (:REWRITE DEFAULT-CDR))
 (894 894 (:REWRITE DEFAULT-CAR))
 (786 92 (:DEFINITION HEAD-EQUAL))
 (14 14 (:REWRITE CONS-CAR-CDR))
 )
(RUN-STK_TERMIANTES_ON_RUN-STK
 (1236 1227 (:REWRITE DEFAULT-CDR))
 (1032 1023 (:REWRITE DEFAULT-CAR))
 (770 362 (:REWRITE DEFAULT-+-2))
 (471 362 (:REWRITE DEFAULT-+-1))
 (144 144 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (66 33 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (38 38 (:REWRITE NOT-CONSP-IMPLICATION))
 (33 33 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 14 (:REWRITE CONS-CAR-CDR))
 )
(OPEN_RUN-STK_MEASURE_CHECK
 (51 51 (:REWRITE DEFAULT-CDR))
 (51 51 (:REWRITE DEFAULT-CAR))
 (36 4 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE RUN-STK_TERMINATES_FROM_RUN-STK_TERMINATES))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(RUN-STK_MEASURE_ON_RUN-STK
 (3982 3691 (:REWRITE DEFAULT-CDR))
 (3588 3297 (:REWRITE DEFAULT-CAR))
 (1902 900 (:REWRITE DEFAULT-+-2))
 (1160 900 (:REWRITE DEFAULT-+-1))
 (738 369 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (369 369 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (228 84 (:REWRITE NOT-CONSP-IMPLICATION))
 (210 210 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (18 18 (:REWRITE CONS-CAR-CDR))
 )
(RUN-STK_MEASURE_REDUCTION
 (33 2 (:REWRITE RUN-STK_TERMINATES_FROM_RUN-STK_TERMINATES))
 (24 3 (:DEFINITION HEAD-EQUAL))
 (9 9 (:TYPE-PRESCRIPTION HEAD-EQUAL))
 (7 1 (:DEFINITION RUN-STK))
 (6 6 (:REWRITE OPEN_RUN-STK_MEASURE_CHECK))
 (5 5 (:REWRITE NOT-CONSP-IMPLICATION))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:DEFINITION BASE-COMPUTATION))
 (1 1 (:DEFINITION BASE))
 )
(RUN-STK_ON_RUN-STK
 (2071 1786 (:REWRITE DEFAULT-CDR))
 (1897 1612 (:REWRITE DEFAULT-CAR))
 (966 483 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (656 308 (:REWRITE DEFAULT-+-2))
 (572 164 (:REWRITE NOT-CONSP-IMPLICATION))
 (483 483 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (399 308 (:REWRITE DEFAULT-+-1))
 (246 246 (:REWRITE OPEN_RUN-STK_TERMINATES))
 )
(RUN-STK_REDUCTION
 (35 4 (:REWRITE RUN-STK_TERMINATES_FROM_RUN-STK_TERMINATES))
 (27 3 (:DEFINITION RUN-STK))
 (24 3 (:DEFINITION HEAD-EQUAL))
 (9 9 (:TYPE-PRESCRIPTION HEAD-EQUAL))
 (6 6 (:REWRITE OPEN_RUN-STK_TERMINATES))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE NOT-CONSP-IMPLICATION))
 (5 5 (:DEFINITION BASE-COMPUTATION))
 (3 3 (:DEFINITION BASE))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 )
(RUN)
(RUN_TERMINATES)
(RUN_MEASURE)
(RUN_SPEC
 (238 238 (:REWRITE DEFAULT-CDR))
 (168 168 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE NOT-CONSP-IMPLICATION))
 )
(RUN_MEASURE_SPEC
 (356 356 (:REWRITE DEFAULT-CDR))
 (248 248 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE OPEN_RUN-STK_MEASURE_CHECK))
 (50 6 (:DEFINITION RUN-STK))
 (41 17 (:REWRITE DEFAULT-+-2))
 (23 17 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE NOT-CONSP-IMPLICATION))
 (8 8 (:DEFINITION BASE-COMPUTATION))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 )
