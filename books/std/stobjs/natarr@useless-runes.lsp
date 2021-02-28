(STOBJS::1D-ARR-TMP-EQUIV)
(STOBJS::1D-ARR-TMP-EQUIV-REFL)
(STOBJS::1D-ARR-TMP-EQUIV-SYMM)
(STOBJS::1D-ARR-TMP-EQUIV-TRANS)
(1D-ARR-TMP-EQUIV-IS-AN-EQUIVALENCE)
(STOBJS::1D-ARR-TMP-LISTP)
(NATP-NTH-OF-1D-ARR-TMP-LISTP
     (96 7 (:REWRITE NTH-WITH-LARGE-INDEX))
     (69 15 (:REWRITE NATP-WHEN-GTE-0))
     (57 15 (:REWRITE NATP-RW))
     (56 14
         (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
     (42 7 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
     (41 30 (:REWRITE DEFAULT-<-2))
     (40 40
         (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
     (36 4 (:REWRITE NATP-OF-NTH-WHEN-NAT-LISTP))
     (35 30 (:REWRITE DEFAULT-<-1))
     (30 30
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (30 30
         (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
     (29 15 (:REWRITE NATP-WHEN-INTEGERP))
     (27 15 (:REWRITE DEFAULT-+-2))
     (26 9 (:REWRITE NFIX-WHEN-NOT-NATP))
     (20 20 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (18 6 (:REWRITE ZP-WHEN-GT-0))
     (15 15 (:REWRITE DEFAULT-+-1))
     (14 7
         (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (14 7
         (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (12 12 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (12 2
         (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
     (10 10 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE ZP-WHEN-INTEGERP))
     (6 6 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE INEQUALITY-WITH-NFIX-HYP-2)))
(STOBJS::1D-ARR-TMP-LISTP-OF-UPDATE-NTH
     (200 23 (:REWRITE NATP-WHEN-GTE-0))
     (184 23 (:REWRITE NATP-RW))
     (157 22
          (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
     (156 11
          (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
     (97 23 (:REWRITE NATP-WHEN-INTEGERP))
     (61 61
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (56 56
         (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
     (54 35 (:REWRITE DEFAULT-<-1))
     (54 28 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (46 46
         (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
     (42 8 (:REWRITE NAT-LISTP-OF-UPDATE-NTH))
     (39 19 (:REWRITE DEFAULT-CDR))
     (39 19 (:REWRITE DEFAULT-CAR))
     (38 35 (:REWRITE DEFAULT-<-2))
     (35 11
         (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (35 11
         (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (22 7 (:REWRITE NFIX-WHEN-NOT-NATP))
     (18 6 (:REWRITE ZP-WHEN-GT-0))
     (15 9 (:REWRITE DEFAULT-+-2))
     (12 2
         (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
     (9 9 (:REWRITE DEFAULT-+-1))
     (6 6 (:REWRITE ZP-WHEN-INTEGERP))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (2 2
        (:REWRITE INEQUALITY-WITH-NFIX-HYP-1)))
(STOBJS::1D-ARR-TMP-LISTP-OF-RESIZE-LIST)
(NATS$CP-OF-UPDATE-NTH (168 13
                            (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                       (156 11
                            (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
                       (76 8 (:REWRITE NAT-LISTP-OF-UPDATE-NTH))
                       (74 34 (:REWRITE DEFAULT-CAR))
                       (72 72
                           (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
                       (62 36 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
                       (56 56
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                       (45 39 (:REWRITE DEFAULT-<-1))
                       (42 39 (:REWRITE DEFAULT-<-2))
                       (41 21 (:REWRITE DEFAULT-CDR))
                       (24 4
                           (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
                       (22 7 (:REWRITE NFIX-WHEN-NOT-NATP))
                       (18 6 (:REWRITE ZP-WHEN-GT-0))
                       (15 9 (:REWRITE DEFAULT-+-2))
                       (9 9 (:REWRITE DEFAULT-+-1))
                       (8 8 (:TYPE-PRESCRIPTION NATP))
                       (8 8
                          (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
                       (8 4 (:REWRITE NATP-WHEN-GTE-0))
                       (6 6 (:REWRITE ZP-WHEN-INTEGERP))
                       (6 6 (:REWRITE ZP-OPEN))
                       (6 6 (:LINEAR LEQ-POSITION-EQUAL-LEN))
                       (4 4 (:REWRITE NATP-WHEN-INTEGERP))
                       (4 4 (:REWRITE NATP-RW))
                       (2 2
                          (:REWRITE INEQUALITY-WITH-NFIX-HYP-1)))
(NATS$CP-OF-RESIZE-LIST)
(NATARR$AP)
(NATARR$AP-REWRITE-TO-1D-ARR-TMP-LISTP
     (48 12
         (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
     (42 6 (:REWRITE NATP-RW))
     (40 6 (:REWRITE NATP-WHEN-GTE-0))
     (36 6 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
     (26 26
         (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
     (18 6 (:REWRITE NATP-WHEN-INTEGERP))
     (16 6
         (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (13 13 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (12 12
         (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
     (12 6
         (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (10 10 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE DEFAULT-CDR)))
(CREATE-NATARR$A)
(NATS$A-LENGTH)
(RESIZE-NATS$A)
(NATS$AI)
(UPDATE-NATS$AI)
(NATARR$CORR)
(CREATE-NATARR{CORRESPONDENCE})
(CREATE-NATARR{PRESERVED})
(NATS-LENGTH{CORRESPONDENCE})
(GET-NAT{CORRESPONDENCE} (59 6 (:REWRITE NTH-WITH-LARGE-INDEX))
                         (30 6 (:DEFINITION LEN))
                         (28 1
                             (:DEFINITION STOBJS::1D-ARR-TMP-LISTP))
                         (14 3 (:REWRITE NFIX-WHEN-NOT-NATP))
                         (12 6 (:REWRITE DEFAULT-+-2))
                         (11 7 (:REWRITE DEFAULT-<-2))
                         (8 8 (:TYPE-PRESCRIPTION NAT-LISTP))
                         (8 2 (:REWRITE NATP-WHEN-GTE-0))
                         (8 2 (:REWRITE NATP-RW))
                         (8 2
                            (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
                         (7 7 (:REWRITE DEFAULT-CDR))
                         (7 7 (:REWRITE DEFAULT-<-1))
                         (6 6 (:REWRITE DEFAULT-+-1))
                         (6 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
                         (4 4
                            (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                         (4 4
                            (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                         (4 4
                            (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
                         (4 4
                            (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
                         (4 4 (:LINEAR LEQ-POSITION-EQUAL-LEN))
                         (4 2 (:REWRITE NATP-WHEN-INTEGERP))
                         (2 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
                         (2 1 (:REWRITE NATP-OF-NTH-WHEN-NAT-LISTP))
                         (2 1
                            (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                         (2 1
                            (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                         (1 1 (:REWRITE DEFAULT-CAR)))
(GET-NAT{GUARD-THM})
(SET-NAT{CORRESPONDENCE} (72 6 (:REWRITE NTH-WITH-LARGE-INDEX))
                         (35 6 (:DEFINITION LEN))
                         (28 1
                             (:DEFINITION STOBJS::1D-ARR-TMP-LISTP))
                         (19 14 (:REWRITE DEFAULT-<-2))
                         (17 10 (:REWRITE DEFAULT-+-2))
                         (16 16 (:REWRITE DEFAULT-CDR))
                         (14 14 (:REWRITE DEFAULT-<-1))
                         (12 3 (:REWRITE ZP-WHEN-INTEGERP))
                         (10 10 (:REWRITE DEFAULT-+-1))
                         (9 3 (:REWRITE ZP-WHEN-GT-0))
                         (8 2
                            (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
                         (7 7 (:TYPE-PRESCRIPTION NAT-LISTP))
                         (7 1 (:REWRITE NATP-WHEN-GTE-0))
                         (7 1 (:REWRITE NATP-RW))
                         (6 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
                         (5 5
                            (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                         (5 5
                            (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                         (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
                         (4 4
                            (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
                         (4 4 (:REWRITE DEFAULT-CAR))
                         (3 1 (:REWRITE NATP-WHEN-INTEGERP))
                         (2 2
                            (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
                         (2 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
                         (2 1
                            (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                         (2 1
                            (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                         (1 1 (:REWRITE NFIX-WHEN-NOT-NATP))
                         (1 1 (:REWRITE CDR-CONS)))
(SET-NAT{GUARD-THM})
(SET-NAT{PRESERVED} (28 1
                        (:DEFINITION STOBJS::1D-ARR-TMP-LISTP))
                    (13 1 (:DEFINITION UPDATE-NTH))
                    (10 2 (:DEFINITION LEN))
                    (8 2
                       (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
                    (7 7 (:TYPE-PRESCRIPTION NAT-LISTP))
                    (7 6 (:REWRITE DEFAULT-<-2))
                    (7 1 (:REWRITE NATP-WHEN-GTE-0))
                    (7 1 (:REWRITE NATP-RW))
                    (6 6 (:REWRITE DEFAULT-<-1))
                    (6 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
                    (5 5 (:REWRITE DEFAULT-CDR))
                    (5 3 (:REWRITE DEFAULT-+-2))
                    (4 4
                       (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
                    (4 1 (:REWRITE ZP-WHEN-INTEGERP))
                    (3 3 (:REWRITE DEFAULT-+-1))
                    (3 1 (:REWRITE ZP-WHEN-GT-0))
                    (3 1 (:REWRITE NATP-WHEN-INTEGERP))
                    (2 2 (:REWRITE NFIX-WHEN-NOT-NATP))
                    (2 2
                       (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
                    (2 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
                    (2 2 (:REWRITE DEFAULT-CAR))
                    (2 1
                       (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                    (2 1
                       (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
                    (1 1 (:LINEAR LEQ-POSITION-EQUAL-LEN)))
(RESIZE-NATS{CORRESPONDENCE}
     (56 4 (:REWRITE NTH-WITH-LARGE-INDEX))
     (28 1
         (:DEFINITION STOBJS::1D-ARR-TMP-LISTP))
     (25 4 (:DEFINITION LEN))
     (10 5 (:REWRITE DEFAULT-+-2))
     (8 2
        (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
     (7 7 (:TYPE-PRESCRIPTION NAT-LISTP))
     (7 7 (:REWRITE DEFAULT-CDR))
     (7 4 (:REWRITE DEFAULT-<-2))
     (7 1 (:REWRITE NATP-WHEN-GTE-0))
     (7 1 (:REWRITE NATP-RW))
     (6 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
     (5 5
        (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (5 5
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (5 5 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
     (4 4 (:REWRITE DEFAULT-<-1))
     (3 3 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (3 1 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2
        (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
     (2 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (2 1
        (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (2 1
        (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
     (1 1 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE CDR-CONS)))
(RESIZE-NATS{PRESERVED})
