(COMPARABLE-MERGESORT-ADMISSION-NTHCDR
     (284 37 (:REWRITE DEFAULT-CDR))
     (274 16 (:REWRITE FLOOR-=-X/Y . 3))
     (274 16 (:REWRITE FLOOR-=-X/Y . 2))
     (231 1 (:REWRITE CONSP-OF-NTHCDR))
     (216 140 (:REWRITE DEFAULT-*-2))
     (188 140 (:REWRITE DEFAULT-*-1))
     (179 76 (:REWRITE DEFAULT-+-2))
     (168 59 (:REWRITE DEFAULT-<-1))
     (146 24 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (136 136
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (136 136
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (134 16 (:REWRITE FLOOR-TYPE-3 . 2))
     (84 59 (:REWRITE DEFAULT-<-2))
     (80 76 (:REWRITE DEFAULT-+-1))
     (59 1 (:REWRITE NTHCDR-WHEN-ZP))
     (54 16 (:REWRITE FLOOR-TYPE-4 . 2))
     (54 16 (:REWRITE FLOOR-TYPE-3 . 3))
     (45 1 (:REWRITE ZP-OPEN))
     (44 44 (:REWRITE INTEGERP-+-MINUS-*))
     (30 16 (:REWRITE FLOOR-TYPE-4 . 3))
     (28 1 (:REWRITE FLOOR-TYPE-2))
     (24 24
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (20 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (17 6 (:LINEAR FLOOR-TYPE-2 . 2))
     (16 5 (:LINEAR FLOOR-TYPE-1 . 2))
     (10 5 (:LINEAR FLOOR-TYPE-1 . 1))
     (3 1 (:REWRITE FLOOR-RECURSION))
     (1 1 (:TYPE-PRESCRIPTION ZP))
     (1 1 (:REWRITE OPEN-SMALL-NTHCDR))
     (1 1 (:REWRITE NTHCDR-WHEN-ATOM)))
(COMPARABLE-MERGESORT-ADMISSION-TAKE
     (32 2 (:REWRITE FLOOR-=-X/Y . 3))
     (32 2 (:REWRITE FLOOR-=-X/Y . 2))
     (24 15 (:REWRITE DEFAULT-*-2))
     (21 15 (:REWRITE DEFAULT-*-1))
     (19 9 (:REWRITE DEFAULT-<-1))
     (18 9 (:REWRITE DEFAULT-+-2))
     (18 2 (:REWRITE FLOOR-TYPE-3 . 2))
     (14 9 (:REWRITE DEFAULT-<-2))
     (13 2 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (10 2 (:REWRITE FLOOR-TYPE-4 . 2))
     (10 2 (:REWRITE FLOOR-TYPE-3 . 3))
     (9 9 (:REWRITE DEFAULT-+-1))
     (9 1 (:REWRITE FLOOR-RECURSION))
     (9 1 (:LINEAR FLOOR-TYPE-2 . 1))
     (7 7 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE INTEGERP-+-MINUS-*))
     (4 2 (:REWRITE FLOOR-TYPE-4 . 3))
     (2 2 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (2 1 (:LINEAR FLOOR-TYPE-2 . 2))
     (2 1 (:LINEAR FLOOR-TYPE-1 . 2))
     (2 1 (:LINEAR FLOOR-TYPE-1 . 1)))
(FAST-MERGESORT-ADMISSION-1 (37 37
                                (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
                            (37 37
                                (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
                            (26 5 (:REWRITE DEFAULT-<-1))
                            (16 2 (:REWRITE FLOOR-=-X/Y . 3))
                            (16 2 (:REWRITE FLOOR-=-X/Y . 2))
                            (12 4 (:REWRITE FOLD-CONSTS-IN-*))
                            (10 10 (:REWRITE DEFAULT-*-2))
                            (10 10 (:REWRITE DEFAULT-*-1))
                            (10 5 (:REWRITE DEFAULT-<-2))
                            (8 2 (:REWRITE FLOOR-TYPE-3 . 2))
                            (6 2 (:REWRITE <-*-/-LEFT-COMMUTED))
                            (6 1 (:REWRITE DEFAULT-UNARY-MINUS))
                            (6 1 (:REWRITE DEFAULT-+-2))
                            (4 4 (:REWRITE INTEGERP-+-MINUS-*))
                            (2 2 (:REWRITE FLOOR-TYPE-4 . 3))
                            (2 2 (:REWRITE FLOOR-TYPE-4 . 2))
                            (2 2 (:REWRITE FLOOR-TYPE-3 . 3))
                            (1 1 (:REWRITE ZP-OPEN))
                            (1 1 (:REWRITE DEFAULT-+-1))
                            (1 1 (:LINEAR FLOOR-TYPE-2 . 2)))
(FAST-MERGESORT-ADMISSION-2 (24 3 (:REWRITE FLOOR-=-X/Y . 3))
                            (24 3 (:REWRITE FLOOR-=-X/Y . 2))
                            (24 1 (:LINEAR FLOOR-TYPE-2 . 1))
                            (16 16 (:REWRITE DEFAULT-*-2))
                            (16 16 (:REWRITE DEFAULT-*-1))
                            (12 7 (:REWRITE DEFAULT-<-1))
                            (12 3 (:REWRITE FLOOR-TYPE-3 . 2))
                            (11 11
                                (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
                            (11 11
                                (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
                            (7 7 (:REWRITE DEFAULT-<-2))
                            (6 6 (:REWRITE INTEGERP-+-MINUS-*))
                            (3 3 (:REWRITE FLOOR-TYPE-4 . 3))
                            (3 3 (:REWRITE FLOOR-TYPE-4 . 2))
                            (3 3 (:REWRITE FLOOR-TYPE-3 . 3))
                            (1 1 (:REWRITE ZP-OPEN))
                            (1 1 (:LINEAR FLOOR-TYPE-2 . 2))
                            (1 1 (:LINEAR FLOOR-TYPE-1 . 2))
                            (1 1 (:LINEAR FLOOR-TYPE-1 . 1)))
(ASH-NEG-1 (268 6 (:REWRITE ASH-0))
           (236 4 (:REWRITE ZIP-OPEN))
           (204 202 (:REWRITE DEFAULT-*-2))
           (202 202 (:REWRITE DEFAULT-*-1))
           (138 138 (:REWRITE DEFAULT-+-2))
           (138 138 (:REWRITE DEFAULT-+-1))
           (125 123 (:REWRITE DEFAULT-<-1))
           (123 123 (:REWRITE DEFAULT-<-2))
           (100 16 (:REWRITE FLOOR-=-X/Y . 3))
           (100 16 (:REWRITE FLOOR-=-X/Y . 2))
           (95 95
               (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
           (95 95
               (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
           (95 95
               (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
           (46 18 (:REWRITE FLOOR-TYPE-4 . 2))
           (46 18 (:REWRITE FLOOR-TYPE-3 . 3))
           (44 2 (:REWRITE FLOOR-=-X/Y . 4))
           (30 30 (:REWRITE INTEGERP-+-MINUS-*))
           (22 2 (:REWRITE EQUAL-*-/-1))
           (20 2 (:REWRITE FLOOR-TYPE-3 . 1))
           (18 18 (:REWRITE FLOOR-TYPE-4 . 3))
           (18 6 (:LINEAR FLOOR-TYPE-2 . 2))
           (18 6 (:LINEAR FLOOR-TYPE-2 . 1))
           (18 6 (:LINEAR FLOOR-TYPE-1 . 2))
           (11 11 (:REWRITE ASH-GOES-TO-0))
           (7 3 (:LINEAR X*Y>1-POSITIVE))
           (6 6 (:TYPE-PRESCRIPTION ZIP))
           (6 6 (:LINEAR FLOOR-TYPE-1 . 1))
           (5 5 (:REWRITE FOLD-CONSTS-IN-+))
           (3 3 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
           (3 3 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
           (3 3 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
           (2 2 (:REWRITE NATP-RW))
           (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
           (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(COMPARABLEP)
(COMPARE<)
(TYPE-OF-COMPARABLEP)
(TYPE-OF-COMPARE<)
(COMPARE<-TRANSITIVE)
(COMPARABLE-LISTP)
(COMPARABLE-LISTP-WHEN-NOT-CONSP)
(COMPARABLE-LISTP-OF-CONS (6 6
                             (:REWRITE COMPARABLE-LISTP-WHEN-NOT-CONSP))
                          (4 4
                             (:REWRITE ELEMENT-LIST-FINAL-CDR-P-REWRITE))
                          (3 3 (:REWRITE DEFAULT-CDR))
                          (3 3 (:REWRITE DEFAULT-CAR)))
(COMPARABLE-LISTP-OF-TAKE (210 12 (:REWRITE TAKE-OF-LEN-FREE))
                          (91 50 (:REWRITE DEFAULT-+-2))
                          (82 82
                              (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                          (78 8 (:REWRITE CONSP-OF-TAKE))
                          (74 19 (:REWRITE ZP-OPEN))
                          (55 55 (:REWRITE DEFAULT-CDR))
                          (50 50 (:REWRITE DEFAULT-+-1))
                          (45 34 (:REWRITE DEFAULT-<-1))
                          (35 34 (:REWRITE DEFAULT-<-2))
                          (33 11 (:REWRITE <-0-+-NEGATIVE-1))
                          (12 4 (:REWRITE FOLD-CONSTS-IN-+))
                          (11 11 (:REWRITE EQUAL-CONSTANT-+))
                          (11 11 (:REWRITE DEFAULT-CAR))
                          (1 1
                             (:REWRITE ELEMENT-LIST-FINAL-CDR-P-REWRITE)))
(COMPARABLE-LISTP-OF-NTHCDR (196 8 (:REWRITE CONSP-OF-NTHCDR))
                            (76 12 (:DEFINITION LEN))
                            (74 74
                                (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                            (55 13 (:REWRITE ZP-OPEN))
                            (48 48 (:TYPE-PRESCRIPTION LEN))
                            (41 25 (:REWRITE DEFAULT-+-2))
                            (40 8 (:DEFINITION NFIX))
                            (36 28 (:REWRITE DEFAULT-<-2))
                            (36 28 (:REWRITE DEFAULT-<-1))
                            (25 25 (:REWRITE DEFAULT-+-1))
                            (18 6 (:REWRITE <-0-+-NEGATIVE-1))
                            (18 6 (:REWRITE <-+-NEGATIVE-0-1))
                            (16 16
                                (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                            (9 9 (:REWRITE OPEN-SMALL-NTHCDR))
                            (9 9 (:REWRITE NTHCDR-WHEN-ATOM))
                            (6 2 (:REWRITE <-+-NEGATIVE-0-2))
                            (1 1
                               (:REWRITE ELEMENT-LIST-FINAL-CDR-P-REWRITE)))
(COMPARABLE-LISTP-OF-CDR)
(COMPARABLEP-OF-CAR)
(COMPARABLE-MERGE (48 23 (:REWRITE DEFAULT-+-2))
                  (30 23 (:REWRITE DEFAULT-+-1))
                  (16 16 (:REWRITE DEFAULT-CDR))
                  (6 2 (:REWRITE DEFAULT-<-2))
                  (6 2 (:REWRITE DEFAULT-<-1))
                  (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                  (4 4 (:REWRITE DEFAULT-CAR))
                  (2 2 (:REWRITE COMPARE<-TRANSITIVE)))
(COMPARABLE-MERGE)
(LEN-OF-COMPARABLE-MERGE (157 79 (:REWRITE DEFAULT-+-2))
                         (100 79 (:REWRITE DEFAULT-+-1))
                         (62 60 (:REWRITE DEFAULT-CDR))
                         (42 42 (:REWRITE DEFAULT-CAR))
                         (32 32
                             (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
                         (17 15 (:REWRITE COMPARE<-TRANSITIVE))
                         (16 16 (:REWRITE EQUAL-CONSTANT-+))
                         (4 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(COMPARABLE-LISTP-OF-COMPARABLE-MERGE
     (22 22 (:REWRITE DEFAULT-CAR))
     (21 21
         (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (10 8 (:REWRITE COMPARE<-TRANSITIVE))
     (6 6 (:REWRITE DEFAULT-CDR)))
(COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT
     (19 19
         (:TYPE-PRESCRIPTION COMPARABLE-MERGE)))
(COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT
     (19 19
         (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (1 1
        (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT)))
(COMPARABLE-MERGE-TR (48 23 (:REWRITE DEFAULT-+-2))
                     (30 23 (:REWRITE DEFAULT-+-1))
                     (16 16 (:REWRITE DEFAULT-CDR))
                     (6 2 (:REWRITE DEFAULT-<-2))
                     (6 2 (:REWRITE DEFAULT-<-1))
                     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                     (4 4 (:REWRITE DEFAULT-CAR))
                     (2 2 (:REWRITE COMPARE<-TRANSITIVE)))
(COMPARABLE-MERGE-TR)
(COMPARABLE-MERGE-TR-REMOVAL-LEMMA
     (698 386 (:REWRITE DEFAULT-CAR))
     (560 248 (:REWRITE DEFAULT-CDR))
     (180 180 (:REWRITE CONSP-OF-REV))
     (88 88
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (88 84 (:REWRITE COMPARE<-TRANSITIVE))
     (60 60 (:REWRITE REV-WHEN-NOT-CONSP)))
(COMPARABLE-MERGE-TR-REMOVAL
     (59 59
         (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (56 14
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (28 14 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (2 2
        (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (2 2
        (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT)))
(FAST-COMPARABLE-MERGESORT-FIXNUMS (43 43
                                       (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
                                   (43 43
                                       (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
                                   (43 43
                                       (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
                                   (31 10 (:REWRITE DEFAULT-<-1))
                                   (21 3 (:REWRITE FLOOR-=-X/Y . 3))
                                   (21 3 (:REWRITE FLOOR-=-X/Y . 2))
                                   (18 6 (:REWRITE COMMUTATIVITY-OF-*))
                                   (15 10 (:REWRITE DEFAULT-<-2))
                                   (12 12 (:REWRITE DEFAULT-*-2))
                                   (12 12 (:REWRITE DEFAULT-*-1))
                                   (9 3 (:REWRITE FLOOR-TYPE-3 . 2))
                                   (6 6 (:REWRITE INTEGERP-+-MINUS-*))
                                   (6 1 (:REWRITE DEFAULT-UNARY-MINUS))
                                   (6 1 (:REWRITE DEFAULT-+-2))
                                   (3 3 (:REWRITE FLOOR-TYPE-4 . 3))
                                   (3 3 (:REWRITE FLOOR-TYPE-4 . 2))
                                   (3 3 (:REWRITE FLOOR-TYPE-3 . 3))
                                   (2 2 (:REWRITE ZP-OPEN))
                                   (1 1 (:REWRITE DEFAULT-+-1))
                                   (1 1 (:LINEAR FLOOR-TYPE-2 . 2)))
(COMPARABLE-LISTP-OF-FAST-COMPARABLE-MERGESORT-FIXNUMS
     (987 8 (:REWRITE ASH-0))
     (910 8 (:REWRITE ZIP-OPEN))
     (686 31 (:REWRITE NTHCDR-WHEN-ZP))
     (572 37 (:REWRITE ZP-OPEN))
     (536 536
          (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (536 536
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (536 536
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (528 9 (:REWRITE NTHCDR-OF-NTHCDR))
     (509 8 (:REWRITE NATP-RW))
     (504 76 (:REWRITE FLOOR-=-X/Y . 3))
     (504 76 (:REWRITE FLOOR-=-X/Y . 2))
     (503 8 (:REWRITE NORMALIZE-EQUAL-0))
     (486 156 (:REWRITE COMMUTATIVITY-OF-*))
     (359 103 (:REWRITE DEFAULT-+-2))
     (316 316 (:REWRITE DEFAULT-*-2))
     (316 316 (:REWRITE DEFAULT-*-1))
     (301 215 (:REWRITE DEFAULT-<-2))
     (252 215 (:REWRITE DEFAULT-<-1))
     (241 76 (:REWRITE FLOOR-TYPE-3 . 2))
     (192 103 (:REWRITE DEFAULT-+-1))
     (168 8 (:REWRITE FLOOR-FLOOR-INTEGER))
     (144 144 (:REWRITE INTEGERP-+-MINUS-*))
     (129 36 (:REWRITE DEFAULT-UNARY-MINUS))
     (120 16 (:REWRITE FLOOR-=-X/Y . 4))
     (114 9 (:REWRITE CAR-OF-NTHCDR))
     (105 9 (:DEFINITION NTH))
     (76 76 (:REWRITE FLOOR-TYPE-4 . 3))
     (76 76 (:REWRITE FLOOR-TYPE-4 . 2))
     (76 76 (:REWRITE FLOOR-TYPE-3 . 3))
     (63 9 (:REWRITE COMMUTATIVITY-OF-+))
     (39 24 (:DEFINITION FIX))
     (39 9
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (34 34 (:LINEAR FLOOR-TYPE-2 . 2))
     (34 34 (:LINEAR FLOOR-TYPE-1 . 2))
     (34 34 (:LINEAR FLOOR-TYPE-1 . 1))
     (32 32 (:REWRITE DEFAULT-CDR))
     (31 31 (:REWRITE OPEN-SMALL-NTHCDR))
     (31 31 (:REWRITE NTHCDR-WHEN-ATOM))
     (31 8
         (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
     (25 25
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (25 25
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (20 20 (:REWRITE FLOOR-RECURSION))
     (18 2 (:REWRITE DISTRIBUTIVITY))
     (17 2 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (16 16 (:TYPE-PRESCRIPTION NATP))
     (16 8 (:REWRITE EQUAL-*-/-1))
     (11 11 (:REWRITE DEFAULT-CAR))
     (9 9 (:REWRITE FOLD-CONSTS-IN-+))
     (9 9 (:REWRITE EQUAL-CONSTANT-+))
     (8 8 (:TYPE-PRESCRIPTION ZIP))
     (8 8 (:REWRITE CANCEL-EQUAL-+-*))
     (8 8 (:REWRITE ASH-GOES-TO-0))
     (8 2
        (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT))
     (7 1
        (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
     (3 3 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
     (3 3 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
     (3 3 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (2 2
        (:REWRITE ELEMENT-LIST-FINAL-CDR-P-REWRITE)))
(FAST-COMPARABLE-MERGESORT-FIXNUMS)
(FAST-COMPARABLE-MERGESORT-FIXNUMS-GUARDS
     (361 361
          (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (361 361
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (361 361
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (198 198 (:REWRITE DEFAULT-*-2))
     (198 198 (:REWRITE DEFAULT-*-1))
     (192 126 (:REWRITE DEFAULT-<-2))
     (182 26 (:REWRITE FLOOR-=-X/Y . 3))
     (182 26 (:REWRITE FLOOR-=-X/Y . 2))
     (179 126 (:REWRITE DEFAULT-<-1))
     (172 114 (:REWRITE DEFAULT-+-2))
     (136 2 (:REWRITE DIFFERENCE-UNSIGNED-BYTE-P))
     (116 114 (:REWRITE DEFAULT-+-1))
     (78 26 (:REWRITE FLOOR-TYPE-3 . 2))
     (58 13 (:REWRITE DEFAULT-UNARY-MINUS))
     (54 54 (:REWRITE INTEGERP-+-MINUS-*))
     (30 9 (:REWRITE FALSIFY-SIGNED-BYTE-P))
     (26 26 (:REWRITE FLOOR-TYPE-4 . 3))
     (26 26 (:REWRITE FLOOR-TYPE-4 . 2))
     (26 26 (:REWRITE FLOOR-TYPE-3 . 3))
     (26 2 (:REWRITE NTHCDR-WHEN-ZP))
     (22 10 (:REWRITE ZP-OPEN))
     (18 18 (:LINEAR FLOOR-TYPE-2 . 2))
     (18 18 (:LINEAR FLOOR-TYPE-1 . 2))
     (18 18 (:LINEAR FLOOR-TYPE-1 . 1))
     (16 16 (:REWRITE DEFAULT-CDR))
     (12 12
         (:REWRITE COMPARABLE-LISTP-WHEN-NOT-CONSP))
     (9 9 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
     (9 9 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
     (9 9 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
     (7 7 (:REWRITE FLOOR-RECURSION))
     (7 1 (:REWRITE FLOOR-TYPE-2))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
     (2 2 (:REWRITE NTHCDR-WHEN-ATOM))
     (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(FAST-COMPARABLE-MERGESORT-FIXNUMS)
(FAST-COMPARABLE-MERGESORT-INTEGERS
     (43 43
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (43 43
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (43 43
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (31 10 (:REWRITE DEFAULT-<-1))
     (21 3 (:REWRITE FLOOR-=-X/Y . 3))
     (21 3 (:REWRITE FLOOR-=-X/Y . 2))
     (18 6 (:REWRITE COMMUTATIVITY-OF-*))
     (15 10 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-*-2))
     (12 12 (:REWRITE DEFAULT-*-1))
     (9 3 (:REWRITE FLOOR-TYPE-3 . 2))
     (6 6 (:REWRITE INTEGERP-+-MINUS-*))
     (6 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 1 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE FLOOR-TYPE-4 . 3))
     (3 3 (:REWRITE FLOOR-TYPE-4 . 2))
     (3 3 (:REWRITE FLOOR-TYPE-3 . 3))
     (2 2 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:LINEAR FLOOR-TYPE-2 . 2)))
(COMPARABLE-LISTP-OF-FAST-COMPARABLE-MERGESORT-INTEGERS
     (1030 1030
           (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (1030 1030
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (1030 1030
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (537 111 (:REWRITE FLOOR-=-X/Y . 3))
     (537 111 (:REWRITE FLOOR-=-X/Y . 2))
     (390 390 (:REWRITE DEFAULT-*-2))
     (390 390 (:REWRITE DEFAULT-*-1))
     (369 234 (:REWRITE DEFAULT-<-1))
     (339 207 (:REWRITE DEFAULT-+-2))
     (300 36 (:REWRITE NTHCDR-WHEN-ZP))
     (280 234 (:REWRITE DEFAULT-<-2))
     (259 111 (:REWRITE FLOOR-TYPE-3 . 2))
     (207 207 (:REWRITE DEFAULT-+-1))
     (157 25 (:REWRITE ZP-OPEN))
     (153 45
          (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (144 144 (:REWRITE INTEGERP-+-MINUS-*))
     (141 61 (:REWRITE DEFAULT-UNARY-MINUS))
     (111 111 (:REWRITE FLOOR-TYPE-4 . 3))
     (111 111 (:REWRITE FLOOR-TYPE-4 . 2))
     (111 111 (:REWRITE FLOOR-TYPE-3 . 3))
     (82 19
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (77 11 (:REWRITE FLOOR-TYPE-2))
     (64 19
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (43 43 (:REWRITE DEFAULT-CDR))
     (36 36 (:REWRITE OPEN-SMALL-NTHCDR))
     (36 36 (:REWRITE NTHCDR-WHEN-ATOM))
     (13 13 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
     (12 12 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
     (12 12 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
     (12 12 (:LINEAR FLOOR-TYPE-2 . 2))
     (12 12 (:LINEAR FLOOR-TYPE-1 . 2))
     (12 12 (:LINEAR FLOOR-TYPE-1 . 1))
     (2 2
        (:REWRITE ELEMENT-LIST-FINAL-CDR-P-REWRITE))
     (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE EQUAL-CONSTANT-+))
     (1 1 (:REWRITE DEFAULT-CAR)))
(CROCK (4193 98 (:REWRITE ZP-OPEN))
       (4113 60 (:REWRITE NTHCDR-WHEN-ZP))
       (2595 2340
             (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
       (2510 67 (:LINEAR FLOOR-TYPE-2 . 1))
       (2340 2340
             (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
       (2340 2340
             (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
       (2121 13 (:REWRITE ASH-0))
       (1934 13 (:REWRITE ZIP-OPEN))
       (1738 246 (:REWRITE COMMUTATIVITY-OF-*))
       (1582 111 (:REWRITE FLOOR-=-X/Y . 2))
       (1437 204 (:REWRITE DEFAULT-+-2))
       (1426 111 (:REWRITE FLOOR-=-X/Y . 3))
       (1227 460 (:REWRITE DEFAULT-<-2))
       (1096 13 (:REWRITE NATP-RW))
       (1045 13 (:REWRITE NORMALIZE-EQUAL-0))
       (958 135
            (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
       (927 22 (:REWRITE CANCEL-FLOOR-+-BASIC))
       (904 556 (:REWRITE DEFAULT-*-2))
       (874 32 (:REWRITE DISTRIBUTIVITY))
       (791 111 (:REWRITE FLOOR-TYPE-3 . 2))
       (773 204 (:REWRITE DEFAULT-+-1))
       (714 23 (:DEFINITION NTH))
       (703 46
            (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
       (689 460 (:REWRITE DEFAULT-<-1))
       (682 556 (:REWRITE DEFAULT-*-1))
       (635 635 (:TYPE-PRESCRIPTION ASH))
       (585 49 (:REWRITE FLOOR-TYPE-2))
       (475 96 (:REWRITE DEFAULT-UNARY-MINUS))
       (467 266 (:REWRITE INTEGERP-+-MINUS-*))
       (424 46
            (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
       (412 35
            (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT))
       (337 27 (:REWRITE FLOOR-=-X/Y . 4))
       (218 11
            (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
       (134 3 (:REWRITE COMMUTATIVITY-2-OF-+))
       (129 111 (:REWRITE FLOOR-TYPE-4 . 3))
       (129 111 (:REWRITE FLOOR-TYPE-4 . 2))
       (129 111 (:REWRITE FLOOR-TYPE-3 . 3))
       (93 3 (:REWRITE CANCEL-FLOOR-+-3))
       (84 39 (:DEFINITION FIX))
       (71 13
           (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
       (67 67 (:LINEAR FLOOR-TYPE-2 . 2))
       (67 67 (:LINEAR FLOOR-TYPE-1 . 2))
       (67 67 (:LINEAR FLOOR-TYPE-1 . 1))
       (60 60 (:REWRITE OPEN-SMALL-NTHCDR))
       (60 60 (:REWRITE NTHCDR-WHEN-ATOM))
       (53 38
           (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
       (38 38 (:REWRITE FOLD-CONSTS-IN-+))
       (26 26 (:TYPE-PRESCRIPTION NATP))
       (26 13 (:REWRITE EQUAL-*-/-1))
       (25 25
           (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
       (24 24 (:REWRITE DEFAULT-CAR))
       (23 23 (:REWRITE DEFAULT-CDR))
       (21 21 (:REWRITE EQUAL-CONSTANT-+))
       (13 13 (:TYPE-PRESCRIPTION ZIP))
       (13 13 (:REWRITE CANCEL-EQUAL-+-*))
       (13 13 (:REWRITE ASH-GOES-TO-0)))
(FAST-COMPARABLE-MERGESORT-INTEGERS)
(FAST-COMPARABLE-MERGESORT-INTEGERS-GUARDS
     (741 741
          (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (741 741
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (741 741
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (554 257 (:REWRITE DEFAULT-<-1))
     (472 340 (:REWRITE DEFAULT-+-2))
     (404 404 (:REWRITE DEFAULT-*-2))
     (404 404 (:REWRITE DEFAULT-*-1))
     (358 257 (:REWRITE DEFAULT-<-2))
     (345 340 (:REWRITE DEFAULT-+-1))
     (212 32 (:REWRITE FLOOR-=-X/Y . 3))
     (212 32 (:REWRITE FLOOR-=-X/Y . 2))
     (129 9 (:REWRITE NTHCDR-WHEN-ZP))
     (128 38 (:REWRITE DEFAULT-UNARY-MINUS))
     (92 32 (:REWRITE FLOOR-TYPE-3 . 2))
     (77 17 (:REWRITE ZP-OPEN))
     (66 66 (:REWRITE INTEGERP-+-MINUS-*))
     (40 40 (:REWRITE DEFAULT-CDR))
     (35 5 (:REWRITE FLOOR-TYPE-2))
     (32 32 (:REWRITE FLOOR-TYPE-4 . 3))
     (32 32 (:REWRITE FLOOR-TYPE-4 . 2))
     (32 32 (:REWRITE FLOOR-TYPE-3 . 3))
     (32 32
         (:REWRITE COMPARABLE-LISTP-WHEN-NOT-CONSP))
     (19 19 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
     (15 15 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
     (15 15 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
     (15 15 (:LINEAR FLOOR-TYPE-2 . 2))
     (15 15 (:LINEAR FLOOR-TYPE-1 . 2))
     (15 15 (:LINEAR FLOOR-TYPE-1 . 1))
     (13 2 (:REWRITE FALSIFY-SIGNED-BYTE-P))
     (9 9 (:REWRITE OPEN-SMALL-NTHCDR))
     (9 9 (:REWRITE NTHCDR-WHEN-ATOM))
     (6 1 (:REWRITE FLOOR-UNSIGNED-BYTE-P))
     (6 1 (:REWRITE DIFFERENCE-UNSIGNED-BYTE-P))
     (4 4 (:REWRITE FLOOR-RECURSION))
     (3 3 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (3 3 (:REWRITE EQUAL-CONSTANT-+)))
(FAST-COMPARABLE-MERGESORT-INTEGERS)
(COMPARABLE-MERGESORT
     (100 43 (:REWRITE DEFAULT-+-2))
     (78 9 (:REWRITE COMMUTATIVITY-OF-*))
     (60 3 (:REWRITE FLOOR-=-X/Y . 3))
     (60 3 (:REWRITE FLOOR-=-X/Y . 2))
     (53 17 (:REWRITE DEFAULT-<-1))
     (47 43 (:REWRITE DEFAULT-+-1))
     (42 6 (:REWRITE DISTRIBUTIVITY))
     (41 41
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (41 41
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (39 24 (:REWRITE DEFAULT-*-2))
     (39 6 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (36 36 (:REWRITE DEFAULT-CDR))
     (33 24 (:REWRITE DEFAULT-*-1))
     (27 3 (:REWRITE FLOOR-TYPE-3 . 2))
     (21 17 (:REWRITE DEFAULT-<-2))
     (18 2 (:LINEAR FLOOR-TYPE-2 . 1))
     (9 9 (:REWRITE INTEGERP-+-MINUS-*))
     (7 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 6 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (6 3 (:REWRITE FLOOR-TYPE-4 . 3))
     (6 3 (:REWRITE FLOOR-TYPE-4 . 2))
     (6 3 (:REWRITE FLOOR-TYPE-3 . 3))
     (4 2 (:LINEAR FLOOR-TYPE-2 . 2))
     (4 2 (:LINEAR FLOOR-TYPE-1 . 2))
     (4 2 (:LINEAR FLOOR-TYPE-1 . 1))
     (2 1
        (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(DUPLICITY-OF-PIECES (1036 320 (:REWRITE DEFAULT-CDR))
                     (730 42 (:REWRITE CONSP-OF-NTHCDR))
                     (566 103 (:REWRITE CONSP-OF-TAKE))
                     (556 556
                          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                     (507 82 (:REWRITE DUPLICITY-WHEN-NOT-CONSP))
                     (386 241 (:REWRITE DEFAULT-+-2))
                     (377 340 (:REWRITE DEFAULT-<-1))
                     (370 340 (:REWRITE DEFAULT-<-2))
                     (321 41 (:REWRITE CAR-OF-TAKE))
                     (281 241 (:REWRITE DEFAULT-+-1))
                     (214 213 (:REWRITE DEFAULT-CAR))
                     (208 208
                          (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
                     (161 13
                          (:REWRITE NTHCDR-WHEN-LESS-THAN-LEN-UNDER-IFF))
                     (105 35 (:REWRITE <-+-NEGATIVE-0-1))
                     (99 99
                         (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                     (91 13 (:REWRITE CAR-OF-NTHCDR))
                     (78 13 (:DEFINITION NTH))
                     (66 41 (:REWRITE TAKE-UNDER-IFF))
                     (36 36 (:REWRITE NTHCDR-WHEN-ATOM))
                     (27 9 (:REWRITE <-+-NEGATIVE-0-2))
                     (19 19 (:REWRITE EQUAL-CONSTANT-+))
                     (9 3 (:REWRITE <-0-+-NEGATIVE-2))
                     (5 5 (:REWRITE CDR-CONS)))
(DUPLICITY-OF-COMPARABLE-MERGE (425 419 (:REWRITE DEFAULT-CAR))
                               (388 388
                                    (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
                               (301 295 (:REWRITE DEFAULT-CDR))
                               (226 118 (:REWRITE DUPLICITY-WHEN-NOT-CONSP))
                               (119 60 (:REWRITE DEFAULT-+-2))
                               (100 60 (:REWRITE DEFAULT-+-1))
                               (51 49 (:REWRITE COMPARE<-TRANSITIVE))
                               (30 30 (:REWRITE EQUAL-CONSTANT-+))
                               (8 8 (:REWRITE CDR-CONS))
                               (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(DUPLICITY-OF-COMPARABLE-MERGESORT
     (848 5 (:REWRITE CONSP-OF-NTHCDR))
     (357 12 (:REWRITE ZP-OPEN))
     (335 53 (:REWRITE DEFAULT-CDR))
     (334 22 (:REWRITE DUPLICITY-WHEN-NOT-CONSP))
     (222 12 (:REWRITE FLOOR-TYPE-2))
     (210 5 (:REWRITE CONSP-OF-TAKE))
     (193 135 (:REWRITE DEFAULT-<-1))
     (189 20 (:REWRITE FLOOR-=-X/Y . 3))
     (189 20 (:REWRITE FLOOR-=-X/Y . 2))
     (177 3 (:REWRITE NTHCDR-WHEN-ZP))
     (176 135 (:REWRITE DEFAULT-<-2))
     (131 102 (:REWRITE DEFAULT-*-2))
     (131 102 (:REWRITE DEFAULT-*-1))
     (126 20 (:REWRITE FLOOR-TYPE-3 . 2))
     (124 2
          (:REWRITE NTHCDR-WHEN-LESS-THAN-LEN-UNDER-IFF))
     (108 108
          (:TYPE-PRESCRIPTION COMPARABLE-MERGESORT))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (100 10 (:LINEAR FLOOR-TYPE-2 . 1))
     (98 2 (:REWRITE CAR-OF-TAKE))
     (93 20 (:REWRITE FLOOR-TYPE-3 . 3))
     (83 20 (:REWRITE FLOOR-TYPE-4 . 2))
     (80 2 (:REWRITE CAR-OF-NTHCDR))
     (78 2 (:DEFINITION NTH))
     (74 10
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (67 67 (:REWRITE DEFAULT-CAR))
     (38 38 (:REWRITE INTEGERP-+-MINUS-*))
     (36 10 (:LINEAR FLOOR-TYPE-2 . 2))
     (36 2 (:REWRITE TAKE-UNDER-IFF))
     (32 20 (:REWRITE FLOOR-TYPE-4 . 3))
     (29 5 (:REWRITE FLOOR-RECURSION))
     (26 8 (:LINEAR FLOOR-TYPE-1 . 2))
     (22 8 (:REWRITE DEFAULT-+-2))
     (12 8 (:LINEAR FLOOR-TYPE-1 . 1))
     (12 3
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (12 3
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (11 5
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (9 8 (:REWRITE DEFAULT-+-1))
     (3 3 (:TYPE-PRESCRIPTION ZP))
     (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
     (3 3 (:REWRITE NTHCDR-WHEN-ATOM))
     (1 1 (:REWRITE CDR-CONS)))
(TRUE-LISTP-OF-COMPARABLE-MERGE (24 8 (:DEFINITION TRUE-LISTP))
                                (18 18 (:REWRITE DEFAULT-CAR))
                                (12 12 (:REWRITE DEFAULT-CDR))
                                (9 7 (:REWRITE COMPARE<-TRANSITIVE)))
(TRUE-LISTP-OF-COMPARABLE-MERGESORT
     (2096 262
           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (1512 2 (:REWRITE NTHCDR-OF-NTHCDR))
     (1470 9 (:REWRITE NTHCDR-WHEN-ZP))
     (1468 17 (:REWRITE ZP-OPEN))
     (1096 1096 (:TYPE-PRESCRIPTION LEN))
     (1052 405
           (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (540 20 (:DEFINITION NFIX))
     (445 146 (:REWRITE DEFAULT-<-2))
     (405 405
          (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
     (405 405
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (405 405
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (405 405 (:TYPE-PRESCRIPTION FLOOR))
     (350 12 (:REWRITE FLOOR-=-X/Y . 2))
     (346 12 (:REWRITE FLOOR-=-X/Y . 3))
     (342 8 (:LINEAR FLOOR-TYPE-2 . 1))
     (322 18 (:REWRITE FLOOR-TYPE-1))
     (311 146 (:REWRITE DEFAULT-<-1))
     (292 32 (:REWRITE COMMUTATIVITY-OF-*))
     (285 15 (:REWRITE FLOOR-TYPE-2))
     (264 12 (:REWRITE FLOOR-TYPE-3 . 2))
     (247 53 (:REWRITE DEFAULT-CDR))
     (212 60 (:REWRITE DEFAULT-+-2))
     (208 2 (:REWRITE LEN-OF-NTHCDR))
     (198 4 (:REWRITE CONSP-OF-NTHCDR))
     (194 12 (:REWRITE FLOOR-TYPE-4 . 2))
     (194 12 (:REWRITE FLOOR-TYPE-3 . 3))
     (180 80 (:REWRITE DEFAULT-*-2))
     (174 8 (:LINEAR FLOOR-TYPE-2 . 2))
     (172 6 (:LINEAR FLOOR-TYPE-1 . 2))
     (170 6 (:REWRITE CONSP-OF-TAKE))
     (166 2 (:REWRITE CAR-OF-TAKE))
     (164 80 (:REWRITE DEFAULT-*-1))
     (140 2 (:REWRITE TAKE-FEWER-OF-TAKE-MORE))
     (118 60 (:REWRITE DEFAULT-+-1))
     (116 2 (:REWRITE CAR-OF-NTHCDR))
     (114 2 (:REWRITE FLOOR-FLOOR-INTEGER))
     (114 2 (:DEFINITION NTH))
     (112 16 (:REWRITE DISTRIBUTIVITY))
     (104 16 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (80 10
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (60 2 (:REWRITE COMMUTATIVITY-OF-+))
     (50 12 (:REWRITE FLOOR-TYPE-4 . 3))
     (49 9 (:REWRITE NTHCDR-WHEN-ATOM))
     (42 2 (:REWRITE ASSOCIATIVITY-OF-+))
     (40 6 (:LINEAR FLOOR-TYPE-1 . 1))
     (38 7 (:DEFINITION TRUE-LISTP))
     (32 32 (:REWRITE INTEGERP-+-MINUS-*))
     (32 8
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (32 8
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (24 2 (:REWRITE LEN-OF-TAKE))
     (16 16
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (14 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 4 (:REWRITE FLOOR-RECURSION))
     (9 9 (:TYPE-PRESCRIPTION ZP))
     (9 9 (:REWRITE OPEN-SMALL-NTHCDR))
     (7 7 (:REWRITE DEFAULT-CAR))
     (6 6 (:TYPE-PRESCRIPTION NFIX))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(LEN-OF-COMPARABLE-MERGESORT
     (263 16 (:REWRITE FLOOR-=-X/Y . 3))
     (263 16 (:REWRITE FLOOR-=-X/Y . 2))
     (246 100 (:REWRITE DEFAULT-+-2))
     (224 4 (:REWRITE NTHCDR-WHEN-ZP))
     (204 125 (:REWRITE DEFAULT-*-2))
     (175 32 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (171 125 (:REWRITE DEFAULT-*-1))
     (168 4 (:REWRITE ZP-OPEN))
     (145 145
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (145 145
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (120 16 (:REWRITE FLOOR-TYPE-3 . 2))
     (115 100 (:REWRITE DEFAULT-+-1))
     (100 4 (:REWRITE FLOOR-TYPE-2))
     (85 46 (:REWRITE DEFAULT-<-1))
     (62 62 (:REWRITE DEFAULT-CDR))
     (53 2 (:REWRITE FLOOR-=-X/Y . 4))
     (52 46 (:REWRITE DEFAULT-<-2))
     (39 39 (:REWRITE INTEGERP-+-MINUS-*))
     (32 16 (:REWRITE FLOOR-TYPE-4 . 3))
     (32 16 (:REWRITE FLOOR-TYPE-4 . 2))
     (32 16 (:REWRITE FLOOR-TYPE-3 . 3))
     (27 3 (:LINEAR FLOOR-TYPE-2 . 1))
     (26 26
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (21 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 2
        (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (8 2
        (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (6 6 (:REWRITE EQUAL-CONSTANT-+))
     (6 3 (:LINEAR FLOOR-TYPE-2 . 2))
     (6 3 (:LINEAR FLOOR-TYPE-1 . 2))
     (6 3 (:LINEAR FLOOR-TYPE-1 . 1))
     (4 4 (:TYPE-PRESCRIPTION ZP))
     (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
     (4 4 (:REWRITE NTHCDR-WHEN-ATOM))
     (1 1 (:REWRITE DEFAULT-CAR)))
(CONSP-OF-COMPARABLE-MERGESORT (130 17 (:REWRITE COMMUTATIVITY-OF-*))
                               (92 5 (:REWRITE FLOOR-=-X/Y . 2))
                               (91 14 (:REWRITE CANCEL-FLOOR-+-BASIC))
                               (88 5 (:REWRITE FLOOR-=-X/Y . 3))
                               (84 42 (:REWRITE DEFAULT-+-2))
                               (70 10 (:REWRITE DISTRIBUTIVITY))
                               (63 44 (:REWRITE DEFAULT-*-2))
                               (53 44 (:REWRITE DEFAULT-*-1))
                               (52 52 (:REWRITE DEFAULT-CDR))
                               (48 2 (:REWRITE NTHCDR-WHEN-ZP))
                               (42 42 (:REWRITE DEFAULT-+-1))
                               (20 15 (:REWRITE DEFAULT-<-1))
                               (17 17 (:REWRITE INTEGERP-+-MINUS-*))
                               (17 15 (:REWRITE DEFAULT-<-2))
                               (14 14
                                   (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
                               (14 14
                                   (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
                               (10 10
                                   (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
                               (10 7 (:REWRITE FLOOR-TYPE-4 . 3))
                               (10 7 (:REWRITE FLOOR-TYPE-4 . 2))
                               (10 7 (:REWRITE FLOOR-TYPE-3 . 3))
                               (2 2 (:TYPE-PRESCRIPTION ZP))
                               (2 2 (:REWRITE NTHCDR-WHEN-ATOM))
                               (1 1 (:REWRITE DEFAULT-CAR)))
(COMPARABLE-LISTP-OF-COMPARABLE-MERGESORT
     (2335 15
           (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (1807 7 (:REWRITE CONSP-OF-NTHCDR))
     (489 12 (:REWRITE ZP-OPEN))
     (449 8 (:REWRITE CONSP-OF-TAKE))
     (412 23 (:REWRITE FLOOR-=-X/Y . 3))
     (412 23 (:REWRITE FLOOR-=-X/Y . 2))
     (320 199 (:REWRITE DEFAULT-*-2))
     (309 12 (:REWRITE FLOOR-TYPE-2))
     (277 199 (:REWRITE DEFAULT-*-1))
     (275 1
          (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (250 149 (:REWRITE DEFAULT-<-1))
     (224 4 (:REWRITE NTHCDR-WHEN-ZP))
     (221 34 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (207 23 (:REWRITE FLOOR-TYPE-3 . 2))
     (192 96 (:REWRITE DEFAULT-+-2))
     (191 149 (:REWRITE DEFAULT-<-2))
     (96 96
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (96 96
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (96 96 (:REWRITE DEFAULT-+-1))
     (82 23 (:REWRITE FLOOR-TYPE-4 . 2))
     (82 23 (:REWRITE FLOOR-TYPE-3 . 3))
     (72 8 (:LINEAR FLOOR-TYPE-2 . 1))
     (63 63 (:REWRITE INTEGERP-+-MINUS-*))
     (60 1
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (56 7
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (54 54 (:REWRITE DEFAULT-CDR))
     (46 23 (:REWRITE FLOOR-TYPE-4 . 3))
     (34 34
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (34 8 (:LINEAR FLOOR-TYPE-2 . 2))
     (34 8 (:LINEAR FLOOR-TYPE-1 . 2))
     (20 8
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (16 8 (:LINEAR FLOOR-TYPE-1 . 1))
     (16 4 (:REWRITE FOLD-CONSTS-IN-+))
     (12 4 (:REWRITE FLOOR-RECURSION))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (8 1 (:LINEAR X*Y>1-POSITIVE))
     (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (4 4 (:TYPE-PRESCRIPTION ZP))
     (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
     (4 4 (:REWRITE NTHCDR-WHEN-ATOM))
     (1 1 (:REWRITE DEFAULT-CAR)))
(COMPARABLE-MERGESORT-OF-LIST-FIX
     (8799 38
           (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (5262 20
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (4428 23 (:REWRITE NTHCDR-WHEN-ZP))
     (3653 20
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (3248 3248
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (3248 3248
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (2887 728 (:REWRITE DEFAULT-<-1))
     (2454 728 (:REWRITE DEFAULT-<-2))
     (2033 9 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
     (1927 7 (:REWRITE TRUE-LISTP-OF-NTHCDR))
     (1766 81 (:LINEAR FLOOR-TYPE-2 . 2))
     (1759 74 (:LINEAR FLOOR-TYPE-1 . 2))
     (1465 326 (:REWRITE DEFAULT-+-2))
     (1134 42 (:REWRITE FLOOR-=-X/Y . 2))
     (1113 42 (:REWRITE FLOOR-=-X/Y . 3))
     (952 98 (:REWRITE COMMUTATIVITY-OF-*))
     (940 261 (:REWRITE DEFAULT-CDR))
     (812 42 (:REWRITE FLOOR-TYPE-3 . 2))
     (663 51
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (630 42 (:REWRITE FLOOR-TYPE-4 . 2))
     (630 42 (:REWRITE FLOOR-TYPE-3 . 3))
     (574 252 (:REWRITE DEFAULT-*-2))
     (561 326 (:REWRITE DEFAULT-+-1))
     (518 252 (:REWRITE DEFAULT-*-1))
     (490 7 (:REWRITE TAKE-FEWER-OF-TAKE-MORE))
     (427 74 (:LINEAR FLOOR-TYPE-1 . 1))
     (399 7 (:DEFINITION NTH))
     (392 56 (:REWRITE DISTRIBUTIVITY))
     (378 70 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (177 3
          (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (168 42 (:REWRITE FLOOR-TYPE-4 . 3))
     (164 17 (:REWRITE DEFAULT-UNARY-MINUS))
     (163 23 (:REWRITE NTHCDR-WHEN-ATOM))
     (98 98 (:REWRITE INTEGERP-+-MINUS-*))
     (95 19 (:DEFINITION TRUE-LISTP))
     (56 56
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (23 23 (:REWRITE OPEN-SMALL-NTHCDR))
     (20 20 (:REWRITE FOLD-CONSTS-IN-+))
     (19 19 (:TYPE-PRESCRIPTION ZP))
     (16 16 (:REWRITE DEFAULT-CAR)))
(TAKE-OF-CDR (12 9 (:REWRITE DEFAULT-CDR))
             (8 8
                (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
             (4 4 (:REWRITE DEFAULT-+-1))
             (3 3 (:REWRITE DEFAULT-<-2))
             (3 3 (:REWRITE DEFAULT-<-1))
             (1 1 (:REWRITE DEFAULT-CAR)))
(CROCK (116 6 (:DEFINITION TAKE))
       (72 13 (:REWRITE DEFAULT-CDR))
       (58 58
           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
       (49 13 (:REWRITE ZP-OPEN))
       (40 2 (:REWRITE CONSP-OF-NTHCDR))
       (30 2 (:REWRITE CAR-OF-NTHCDR))
       (28 2 (:DEFINITION NTH))
       (26 22 (:REWRITE DEFAULT-+-2))
       (26 7 (:REWRITE NTHCDR-WHEN-ATOM))
       (23 23
           (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
       (23 22 (:REWRITE DEFAULT-+-1))
       (15 13 (:REWRITE DEFAULT-<-2))
       (15 13 (:REWRITE DEFAULT-<-1))
       (12 4 (:REWRITE <-0-+-NEGATIVE-1))
       (10 10 (:TYPE-PRESCRIPTION LEN))
       (10 2 (:DEFINITION NFIX))
       (10 2 (:DEFINITION LEN))
       (9 7 (:REWRITE FOLD-CONSTS-IN-+))
       (8 4 (:REWRITE CONSP-OF-TAKE))
       (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
       (6 6 (:REWRITE DEFAULT-CAR))
       (6 2 (:REWRITE <-0-+-NEGATIVE-2))
       (6 2 (:REWRITE <-+-NEGATIVE-0-2))
       (2 2 (:REWRITE NATP-RW)))
(NTHCDR-OF-TAKE (18 18
                    (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                (18 4 (:REWRITE NTHCDR-WHEN-ATOM))
                (10 4 (:REWRITE NTHCDR-WHEN-ZP))
                (10 2 (:REWRITE CONSP-OF-TAKE))
                (6 6 (:TYPE-PRESCRIPTION ZP))
                (6 6 (:REWRITE ZP-OPEN))
                (6 6 (:REWRITE DEFAULT-+-2))
                (6 6 (:REWRITE DEFAULT-+-1))
                (4 4
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
                (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                (1 1 (:REWRITE DEFAULT-<-2))
                (1 1 (:REWRITE DEFAULT-<-1)))
(CROCK3 (2 2 (:REWRITE DEFAULT-CDR))
        (2 1 (:REWRITE DEFAULT-+-2))
        (1 1 (:REWRITE DEFAULT-<-2))
        (1 1 (:REWRITE DEFAULT-<-1))
        (1 1 (:REWRITE DEFAULT-+-1)))
(FAST-COMPARABLE-MERGESORT-FIXNUMS-REDEFINITION
     (5256 2 (:REWRITE NATP-RW))
     (3236 536
           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (3027 2381
           (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (2998 8
           (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (2381 2381
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (2381 2381
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (1967 29 (:REWRITE ZP-OPEN))
     (1926 8
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (1416 16 (:REWRITE FLOOR-TYPE-2))
     (1211 215 (:REWRITE DEFAULT-<-1))
     (1190 2 (:REWRITE CONSP-OF-NTHCDR))
     (1104 8
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (1074 12 (:REWRITE NTHCDR-WHEN-ZP))
     (951 69 (:REWRITE FLOOR-=-X/Y . 3))
     (951 69 (:REWRITE FLOOR-=-X/Y . 2))
     (893 215 (:REWRITE DEFAULT-<-2))
     (811 69 (:REWRITE FLOOR-TYPE-3 . 2))
     (711 69 (:REWRITE FLOOR-TYPE-4 . 3))
     (711 69 (:REWRITE FLOOR-TYPE-4 . 2))
     (711 69 (:REWRITE FLOOR-TYPE-3 . 3))
     (572 236 (:REWRITE DEFAULT-*-2))
     (572 236 (:REWRITE DEFAULT-*-1))
     (340 4 (:REWRITE CAR-OF-TAKE))
     (234 20 (:LINEAR FLOOR-TYPE-2 . 2))
     (232 18 (:LINEAR FLOOR-TYPE-1 . 2))
     (232 18 (:LINEAR FLOOR-TYPE-1 . 1))
     (118 26 (:REWRITE DEFAULT-+-2))
     (100 16
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (90 10 (:REWRITE <-+-NEGATIVE-0-2))
     (87 6 (:REWRITE DEFAULT-CDR))
     (84 84 (:REWRITE INTEGERP-+-MINUS-*))
     (60 10 (:REWRITE DEFAULT-UNARY-MINUS))
     (56 2
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (48 12 (:REWRITE NTHCDR-WHEN-ATOM))
     (43 7 (:REWRITE DEFAULT-CAR))
     (42 10 (:REWRITE <-0-+-NEGATIVE-2))
     (42 2 (:REWRITE FLOOR-FLOOR-INTEGER))
     (36 26 (:REWRITE DEFAULT-+-1))
     (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (18 18 (:REWRITE FLOOR-RECURSION))
     (12 12 (:REWRITE OPEN-SMALL-NTHCDR))
     (4 4 (:TYPE-PRESCRIPTION NATP)))
(FAST-COMPARABLE-MERGESORT-INTEGERS-REDEFINITION
     (5256 2 (:REWRITE NATP-RW))
     (3556 12
           (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (3187 2506
           (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (2506 2506
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (2506 2506
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (2412 10
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (1464 3 (:REWRITE CONSP-OF-NTHCDR))
     (1379 312 (:REWRITE DEFAULT-<-1))
     (1233 10
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (1132 15 (:REWRITE NTHCDR-WHEN-ZP))
     (1119 88 (:REWRITE FLOOR-=-X/Y . 3))
     (1119 88 (:REWRITE FLOOR-=-X/Y . 2))
     (1025 312 (:REWRITE DEFAULT-<-2))
     (942 88 (:REWRITE FLOOR-TYPE-3 . 2))
     (779 88 (:REWRITE FLOOR-TYPE-4 . 3))
     (779 88 (:REWRITE FLOOR-TYPE-3 . 3))
     (769 88 (:REWRITE FLOOR-TYPE-4 . 2))
     (692 336 (:REWRITE DEFAULT-*-2))
     (692 336 (:REWRITE DEFAULT-*-1))
     (262 27 (:LINEAR FLOOR-TYPE-2 . 2))
     (260 25 (:LINEAR FLOOR-TYPE-1 . 2))
     (260 25 (:LINEAR FLOOR-TYPE-1 . 1))
     (122 122 (:REWRITE INTEGERP-+-MINUS-*))
     (112 32 (:REWRITE DEFAULT-+-2))
     (96 8 (:REWRITE DEFAULT-CDR))
     (64 3
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (55 15 (:REWRITE NTHCDR-WHEN-ATOM))
     (46 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (43 7 (:REWRITE DEFAULT-CAR))
     (42 32 (:REWRITE DEFAULT-+-1))
     (23 23 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (15 15 (:REWRITE OPEN-SMALL-NTHCDR))
     (6 6 (:TYPE-PRESCRIPTION NATP)))
(FAST-COMPARABLE-MERGESORT-FIXNUMS-OF-LEN-IS-SPEC)
(FAST-COMPARABLE-MERGESORT-INTEGERS-OF-LEN-IS-SPEC)
(COMPARABLE-MERGESORT)
(COMPARABLE-MERGESORT-GUARD
     (520 8
          (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (324 8 (:REWRITE ZP-OPEN))
     (305 5
          (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (256 4 (:REWRITE CONSP-OF-NTHCDR))
     (241 5
          (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (225 5 (:REWRITE NTHCDR-WHEN-ZP))
     (220 4 (:REWRITE CONSP-OF-TAKE))
     (200 8 (:REWRITE FLOOR-TYPE-2))
     (129 79 (:REWRITE DEFAULT-<-1))
     (104 12 (:REWRITE COMMUTATIVITY-OF-*))
     (92 79 (:REWRITE DEFAULT-<-2))
     (84 8 (:REWRITE FLOOR-=-X/Y . 3))
     (84 8 (:REWRITE FLOOR-=-X/Y . 2))
     (82 41 (:REWRITE DEFAULT-+-2))
     (68 4 (:DEFINITION NFIX))
     (60 16 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (56 8 (:REWRITE DISTRIBUTIVITY))
     (53 53
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (53 53
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (52 32 (:REWRITE DEFAULT-*-2))
     (44 32 (:REWRITE DEFAULT-*-1))
     (42 42 (:REWRITE DEFAULT-CDR))
     (41 41 (:REWRITE DEFAULT-+-1))
     (40 8 (:REWRITE FLOOR-TYPE-3 . 2))
     (40 4 (:REWRITE FLOOR-TYPE-1))
     (36 4 (:LINEAR FLOOR-TYPE-2 . 1))
     (32 4
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (16 8 (:REWRITE FLOOR-TYPE-4 . 3))
     (16 8 (:REWRITE FLOOR-TYPE-4 . 2))
     (16 8 (:REWRITE FLOOR-TYPE-3 . 3))
     (12 12 (:REWRITE INTEGERP-+-MINUS-*))
     (12 4 (:REWRITE FLOOR-RECURSION))
     (8 8 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (8 4 (:LINEAR FLOOR-TYPE-2 . 2))
     (8 4 (:LINEAR FLOOR-TYPE-1 . 2))
     (8 4 (:LINEAR FLOOR-TYPE-1 . 1))
     (5 5 (:REWRITE OPEN-SMALL-NTHCDR))
     (5 5 (:REWRITE NTHCDR-WHEN-ATOM))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4 (:TYPE-PRESCRIPTION ZP))
     (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (2 1 (:REWRITE FALSIFY-SIGNED-BYTE-P)))
(COMPARABLE-MERGESORT)
(COMPARABLE-ORDEREDP)
(COMPARABLE-ORDEREDP-WHEN-NOT-CONSP)
(COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR
     (2 2 (:REWRITE DEFAULT-CDR))
     (1 1
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP)))
(COMPARABLE-ORDEREDP-OF-COMPARABLE-MERGE
     (3482 2702 (:REWRITE DEFAULT-CDR))
     (2779 1801 (:REWRITE COMPARE<-TRANSITIVE))
     (884 716
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP)))
(COMPARABLE-ORDEREDP-OF-COMPARABLE-MERGESORT
     (5544 693
           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (4857 36
           (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (3585 41 (:REWRITE ZP-OPEN))
     (2900 21 (:REWRITE CONSP-OF-NTHCDR))
     (2781 1065
           (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (2487 11
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (2276 26 (:REWRITE CONSP-OF-TAKE))
     (2268 3 (:REWRITE NTHCDR-OF-NTHCDR))
     (2118 12 (:REWRITE NTHCDR-WHEN-ZP))
     (1740 11
           (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (1388 38 (:REWRITE FLOOR-TYPE-2))
     (1285 48 (:DEFINITION NFIX))
     (1147 400 (:REWRITE DEFAULT-<-1))
     (1107 33 (:LINEAR FLOOR-TYPE-2 . 1))
     (1065 1065
           (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
     (1065 1065
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (1065 1065
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (1065 1065 (:TYPE-PRESCRIPTION FLOOR))
     (1039 400 (:REWRITE DEFAULT-<-2))
     (762 103 (:REWRITE DEFAULT-CDR))
     (607 42 (:REWRITE FLOOR-TYPE-1))
     (562 33 (:LINEAR FLOOR-TYPE-2 . 2))
     (551 30 (:LINEAR FLOOR-TYPE-1 . 2))
     (548 20 (:REWRITE FLOOR-=-X/Y . 2))
     (539 20 (:REWRITE FLOOR-=-X/Y . 3))
     (476 52 (:REWRITE COMMUTATIVITY-OF-*))
     (384 123 (:REWRITE DEFAULT-+-2))
     (382 20 (:REWRITE FLOOR-TYPE-3 . 2))
     (382 8
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (312 3 (:REWRITE LEN-OF-NTHCDR))
     (300 30
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (286 20 (:REWRITE FLOOR-TYPE-4 . 2))
     (286 20 (:REWRITE FLOOR-TYPE-3 . 3))
     (284 132 (:REWRITE DEFAULT-*-2))
     (256 132 (:REWRITE DEFAULT-*-1))
     (249 3 (:REWRITE CAR-OF-TAKE))
     (210 123 (:REWRITE DEFAULT-+-1))
     (210 3 (:REWRITE TAKE-FEWER-OF-TAKE-MORE))
     (196 28 (:REWRITE DISTRIBUTIVITY))
     (184 30 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (174 3 (:REWRITE CAR-OF-NTHCDR))
     (171 3 (:REWRITE FLOOR-FLOOR-INTEGER))
     (171 3 (:DEFINITION NTH))
     (141 30 (:LINEAR FLOOR-TYPE-1 . 1))
     (111 111
          (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGESORT))
     (90 3 (:REWRITE COMMUTATIVITY-OF-+))
     (76 20 (:REWRITE FLOOR-TYPE-4 . 3))
     (72 12 (:REWRITE NTHCDR-WHEN-ATOM))
     (72 6 (:REWRITE LEN-OF-TAKE))
     (63 3 (:REWRITE ASSOCIATIVITY-OF-+))
     (52 52 (:REWRITE INTEGERP-+-MINUS-*))
     (51 13 (:REWRITE FLOOR-RECURSION))
     (41 41 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (28 28
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (27 27 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (27 9
         (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGE))
     (21 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 12 (:TYPE-PRESCRIPTION ZP))
     (12 12 (:REWRITE OPEN-SMALL-NTHCDR))
     (9 9 (:TYPE-PRESCRIPTION NFIX))
     (9 9 (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (9 9 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+)))
(NO-DUPLICATESP-EQUAL-OF-COMPARABLE-MERGESORT)
(COMPARE<-NEGATION-TRANSITIVE)
(COMPARE<-NEGATION-TRANSITIVE-NECC (6 6 (:DEFINITION MV-NTH)))
(COMPARE<-STRICT)
(COMPARE<-STRICT-NECC)
(COMPARE<-REVERSE-WHEN-STRICT
     (4 2
        (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (2 2
        (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE)))
(COMPARE-EQUIV-ELTS)
(COMPARE-EQUIV-ELTS-EMPTY-CASE
     (287 125
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (188 188
          (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (92 92 (:REWRITE DEFAULT-CDR))
     (39 13 (:REWRITE COMPARE<-STRICT-NECC))
     (25 25
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP)))
(COMPARE-NEGATION-TRANSITIVE-IMPLIES
     (6 2
        (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (4 4 (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (1 1 (:REWRITE COMPARE<-TRANSITIVE)))
(COMPARE-TRANSITIVE-IMPLIES
     (4 4
        (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (3 1
        (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (3 1
        (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (3 1
        (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (2 2 (:TYPE-PRESCRIPTION COMPARE<-STRICT)))
(COMPARE-EQUIV-ELTS-OF-COMPARABLE-MERGE
     (6149 5271 (:REWRITE DEFAULT-CDR))
     (2167 1657
           (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (576 88
          (:REWRITE COMPARABLE-ORDEREDP-OF-COMPARABLE-MERGE)))
(COMPARE-EQUIV-ELTS-OF-APPEND
     (946 85
          (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (471 84
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (299 147 (:REWRITE DEFAULT-CDR))
     (262 138
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (221 83
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (218 94
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (218 94
          (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (214 94
          (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (184 184 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (167 167
          (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (148 116 (:REWRITE DEFAULT-CAR))
     (124 124
          (:TYPE-PRESCRIPTION COMPARE<-STRICT)))
(APPEND-COMPARE-EXTRACTS-OF-TAKE/NTHCDR
     (374 23
          (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (204 16
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (146 35 (:REWRITE DEFAULT-CDR))
     (111 12
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (96 48
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (72 6 (:REWRITE CONSP-OF-NTHCDR))
     (57 57 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (55 11 (:DEFINITION LEN))
     (28 28
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (23 21 (:REWRITE DEFAULT-<-2))
     (22 11 (:REWRITE DEFAULT-+-2))
     (21 21 (:REWRITE DEFAULT-<-1))
     (17 17 (:REWRITE ZP-OPEN))
     (14 14 (:TYPE-PRESCRIPTION ZP))
     (12 12 (:REWRITE OPEN-SMALL-NTHCDR))
     (12 12 (:REWRITE NTHCDR-WHEN-ATOM))
     (11 11 (:REWRITE DEFAULT-+-1))
     (8 8
        (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (8 8 (:REWRITE DEFAULT-CAR))
     (6 1 (:REWRITE CAR-OF-TAKE)))
(COMPARE-EQUIV-ELTS-OF-COMPARABLE-MERGESORT
     (329 2
          (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (275 1
          (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (263 1 (:REWRITE CONSP-OF-NTHCDR))
     (225 5 (:REWRITE NTHCDR-WHEN-ZP))
     (207 5 (:REWRITE ZP-OPEN))
     (183 12 (:REWRITE FLOOR-=-X/Y . 3))
     (183 12 (:REWRITE FLOOR-=-X/Y . 2))
     (132 81 (:REWRITE DEFAULT-*-2))
     (125 5 (:REWRITE FLOOR-TYPE-2))
     (123 24 (:REWRITE CANCEL-FLOOR-+-BASIC))
     (111 81 (:REWRITE DEFAULT-*-1))
     (102 51 (:REWRITE DEFAULT-+-2))
     (84 12 (:REWRITE FLOOR-TYPE-3 . 2))
     (75 46 (:REWRITE DEFAULT-<-1))
     (60 1
         (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (55 1 (:REWRITE CONSP-OF-TAKE))
     (53 46 (:REWRITE DEFAULT-<-2))
     (51 51 (:REWRITE DEFAULT-+-1))
     (44 44 (:REWRITE DEFAULT-CDR))
     (27 27 (:REWRITE INTEGERP-+-MINUS-*))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (24 18
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (24 12 (:REWRITE FLOOR-TYPE-4 . 3))
     (24 12 (:REWRITE FLOOR-TYPE-4 . 2))
     (24 12 (:REWRITE FLOOR-TYPE-3 . 3))
     (18 18
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (18 2 (:LINEAR FLOOR-TYPE-2 . 1))
     (17 17 (:REWRITE DEFAULT-CAR))
     (16 16 (:REWRITE COMPARE<-TRANSITIVE))
     (10 10
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (8 8
        (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (8 1
        (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (5 5 (:REWRITE OPEN-SMALL-NTHCDR))
     (5 5 (:REWRITE NTHCDR-WHEN-ATOM))
     (5 1 (:DEFINITION BINARY-APPEND))
     (4 4 (:TYPE-PRESCRIPTION ZP))
     (4 2 (:LINEAR FLOOR-TYPE-2 . 2))
     (4 2 (:LINEAR FLOOR-TYPE-1 . 2))
     (4 2 (:LINEAR FLOOR-TYPE-1 . 1))
     (4 1 (:REWRITE FOLD-CONSTS-IN-+))
     (3 1 (:REWRITE FLOOR-RECURSION))
     (2 1
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(COMPARE-ELTS-EQUIV)
(COMPARE-ELTS-EQUIV-NECC)
(UNEQUAL-LISTS-BADGUY)
(COMPARE-EQUIV-ELTS-WHEN-NOT-CONSP
     (5 1
        (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (1 1
        (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (1 1 (:REWRITE COMPARE-ELTS-EQUIV-NECC))
     (1 1
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR)))
(COMPARE-EQUIV-ELTS-WHEN-PAST)
(COMPARE-EQUIV-ELTS-OF-UNEQUAL-LISTS
     (7288 7288 (:REWRITE DEFAULT-CDR))
     (6024 662 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (4491 1791
           (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (4450 988 (:DEFINITION TRUE-LISTP))
     (3603 276
           (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (3218 3218 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (2820 2820
           (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (2040 1020 (:REWRITE DEFAULT-+-2))
     (1052 1052
           (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (1020 1020 (:REWRITE DEFAULT-+-1))
     (624 624 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
     (276 276 (:REWRITE COMPARE-ELTS-EQUIV-NECC))
     (189 69 (:REWRITE COMPARE<-STRICT-NECC)))
(COMPARABLE-INSERT)
(COMPARE-EQUIV-ELTS-OF-COMPARABLE-INSERT
     (1492 157
           (:REWRITE COMPARE-EQUIV-ELTS-WHEN-PAST))
     (848 310
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (802 153
          (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (614 614
          (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (492 304
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (487 283 (:REWRITE DEFAULT-CDR))
     (321 247 (:REWRITE DEFAULT-CAR))
     (62 62 (:REWRITE COMPARE-ELTS-EQUIV-NECC)))
(COMPARABLE-ORDEREDP-OF-COMPARABLE-INSERT
     (768 768
          (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (708 324
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (622 324 (:REWRITE COMPARE<-TRANSITIVE))
     (576 192
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (576 192
          (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (481 371 (:REWRITE DEFAULT-CDR))
     (466 192
          (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (384 384
          (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (134 109
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP)))
(COMPARABLE-LISTP-OF-COMPARABLE-INSERT
     (24 24
         (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (20 8
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (18 6
         (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (18 6
         (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (12 12 (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (12 6 (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (11 8 (:REWRITE COMPARE<-TRANSITIVE))
     (9 9 (:REWRITE DEFAULT-CAR))
     (4 4
        (:TYPE-PRESCRIPTION COMPARABLE-INSERT))
     (2 2 (:REWRITE DEFAULT-CDR)))
(TRUE-LISTP-OF-COMPARABLE-INSERT
     (24 24
         (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (20 8
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (18 6
         (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (18 6
         (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (12 12 (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (12 6 (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (11 8 (:REWRITE DEFAULT-CDR))
     (11 8 (:REWRITE COMPARE<-TRANSITIVE))
     (9 9 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE CDR-CONS)))
(COMPARABLE-INSERTSORT)
(COMPARABLE-LISTP-OF-COMPARABLE-INSERTSORT
     (9 9
        (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (3 3 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE DEFAULT-CDR)))
(COMPARABLE-INSERTSORT)
(COMPARABLE-INSERTSORT-GUARD (1 1 (:REWRITE DEFAULT-CAR))
                             (1 1
                                (:REWRITE COMPARABLE-LISTP-WHEN-NOT-CONSP)))
(COMPARABLE-INSERTSORT)
(COMPARE-EQUIV-ELTS-OF-COMPARABLE-INSERTSORT
     (84 9
         (:REWRITE COMPARE-EQUIV-ELTS-WHEN-PAST))
     (41 16
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (35 7
         (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (30 30
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (23 14
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (19 10 (:REWRITE DEFAULT-CDR))
     (10 10
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (8 8 (:REWRITE COMPARE<-TRANSITIVE))
     (7 7 (:REWRITE COMPARE-ELTS-EQUIV-NECC))
     (6 6 (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4
        (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC)))
(COMPARABLE-ORDEREDP-OF-COMPARABLE-INSERTSORT
     (27 27
         (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (14 5 (:REWRITE DEFAULT-CDR))
     (12 3
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (3 3 (:REWRITE DEFAULT-CAR)))
(TRUE-LISTP-OF-COMPARABLE-INSERTSORT (12 3 (:DEFINITION TRUE-LISTP))
                                     (5 5 (:REWRITE DEFAULT-CDR))
                                     (3 3 (:REWRITE DEFAULT-CAR)))
(COMPARABLE-MERGESORT-EQUALS-COMPARABLE-INSERTSORT
     (78 2 (:DEFINITION UNEQUAL-LISTS-BADGUY))
     (38 17 (:REWRITE DEFAULT-CAR))
     (18 3
         (:REWRITE COMPARE-EQUIV-ELTS-WHEN-PAST))
     (11 5 (:REWRITE DEFAULT-CDR))
     (10 10
         (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (10 2
         (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (6 3
        (:REWRITE COMPARE-EQUIV-ELTS-WHEN-NOT-CONSP))
     (6 2
        (:REWRITE COMPARE-EQUIV-ELTS-EMPTY-CASE))
     (5 5 (:REWRITE COMPARE<-TRANSITIVE))
     (5 5
        (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (3 3 (:REWRITE COMPARE-ELTS-EQUIV-NECC))
     (3 2
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (2 2
        (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (2 2 (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (2 2
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP)))
(SUBSETP-OF-COMPARABLE-MERGE-1
     (154 142 (:REWRITE DEFAULT-CAR))
     (96 96
         (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (96 84 (:REWRITE DEFAULT-CDR))
     (76 28
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (72 36
         (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGE))
     (72 24
         (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (72 24
         (:REWRITE COMPARE<-NEGATION-TRANSITIVE-NECC))
     (48 48 (:TYPE-PRESCRIPTION COMPARE<-STRICT))
     (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (36 36
         (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (36 24
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (34 28 (:REWRITE COMPARE<-TRANSITIVE)))
(COMPARE<-TOTAL)
(COMPARE<-TOTAL-NECC (4 4 (:DEFINITION MV-NTH)))
(NO-DUPLICATESP-EQUAL-OF-REMOVE-DUPLICATES-EQUAL
     (170 10 (:DEFINITION MEMBER-EQUAL))
     (161 23 (:REWRITE SUBSETP-CAR-MEMBER))
     (32 32 (:REWRITE DEFAULT-CDR))
     (30 12
         (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-ATOM))
     (29 29 (:REWRITE SUBSETP-TRANS2))
     (29 29 (:REWRITE SUBSETP-TRANS))
     (26 26 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (26 26 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (25 25 (:REWRITE DEFAULT-CAR))
     (23 23 (:REWRITE SUBSETP-MEMBER . 4))
     (23 23 (:REWRITE INTERSECTP-MEMBER . 3))
     (23 23 (:REWRITE INTERSECTP-MEMBER . 2))
     (21 21 (:REWRITE SUBSETP-MEMBER . 2))
     (21 3
         (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (20 20 (:REWRITE MEMBER-WHEN-ATOM))
     (13 13
         (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-DUPLICITY-BADGUY1))
     (12 12
         (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-HIGH-DUPLICITY)))
(MEMBER-EQUAL-NTH (54 54
                      (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                  (50 5 (:DEFINITION MEMBER-EQUAL))
                  (31 21 (:REWRITE DEFAULT-<-2))
                  (26 15 (:REWRITE DEFAULT-+-2))
                  (24 24 (:REWRITE DEFAULT-CAR))
                  (24 21 (:REWRITE DEFAULT-<-1))
                  (15 15 (:REWRITE DEFAULT-+-1))
                  (13 13 (:REWRITE DEFAULT-CDR))
                  (11 11 (:REWRITE SUBSETP-MEMBER . 4))
                  (11 11 (:REWRITE SUBSETP-MEMBER . 3))
                  (11 11 (:REWRITE SUBSETP-MEMBER . 2))
                  (11 11 (:REWRITE INTERSECTP-MEMBER . 3))
                  (11 11 (:REWRITE INTERSECTP-MEMBER . 2))
                  (10 10 (:REWRITE MEMBER-WHEN-ATOM))
                  (8 8 (:REWRITE ZP-OPEN))
                  (4 4 (:REWRITE SUBSETP-TRANS2))
                  (4 4 (:REWRITE SUBSETP-TRANS))
                  (2 2
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(SUBSETP-OF-COMPARABLE-MERGESORT
     (1326 6 (:REWRITE CONSP-OF-NTHCDR))
     (1168 10
           (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (716 3
          (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-RIGHT))
     (602 7 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (387 9 (:REWRITE ZP-OPEN))
     (348 6 (:REWRITE CONSP-OF-TAKE))
     (301 7 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (252 9 (:REWRITE FLOOR-TYPE-2))
     (246 144 (:REWRITE DEFAULT-<-1))
     (216 18 (:REWRITE FLOOR-=-X/Y . 3))
     (216 18 (:REWRITE FLOOR-=-X/Y . 2))
     (210 144 (:REWRITE DEFAULT-<-2))
     (189 3
          (:REWRITE COMPARABLE-MERGE-WHEN-NOT-CONSP-LEFT))
     (177 3 (:REWRITE NTHCDR-WHEN-ZP))
     (162 18 (:REWRITE FLOOR-TYPE-3 . 2))
     (147 98 (:REWRITE DEFAULT-*-2))
     (147 98 (:REWRITE DEFAULT-*-1))
     (132 18 (:REWRITE FLOOR-TYPE-3 . 3))
     (90 90
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (90 90
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (84 18 (:REWRITE FLOOR-TYPE-4 . 2))
     (64 8
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (63 7 (:LINEAR FLOOR-TYPE-2 . 1))
     (50 7 (:LINEAR FLOOR-TYPE-2 . 2))
     (49 7 (:REWRITE FLOOR-RECURSION))
     (36 36 (:REWRITE INTEGERP-+-MINUS-*))
     (36 18 (:REWRITE FLOOR-TYPE-4 . 3))
     (26 26
         (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGESORT))
     (26 7 (:LINEAR FLOOR-TYPE-1 . 2))
     (23 9
         (:REWRITE COMPARABLE-MERGESORT-EQUALS-COMPARABLE-INSERTSORT))
     (21 7
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (14 14
         (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (14 7 (:LINEAR FLOOR-TYPE-1 . 1))
     (13 13 (:REWRITE SUBSETP-TRANS2))
     (12 6 (:REWRITE DEFAULT-+-2))
     (9 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGE))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (8 1 (:LINEAR X*Y>1-POSITIVE))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE DEFAULT-+-1))
     (3 3 (:TYPE-PRESCRIPTION ZP))
     (3 3 (:TYPE-PRESCRIPTION COMPARABLE-MERGE))
     (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
     (3 3 (:REWRITE NTHCDR-WHEN-ATOM))
     (3 3 (:REWRITE DEFAULT-CAR)))
(COMPARABLE-MERGESORT-IS-IDENTITY-UNDER-SET-EQUIV-LEMMA-3
     (10 1 (:DEFINITION MEMBER-EQUAL))
     (2 2 (:REWRITE SUBSETP-MEMBER . 4))
     (2 2 (:REWRITE SUBSETP-MEMBER . 3))
     (2 2 (:REWRITE SUBSETP-MEMBER . 2))
     (2 2 (:REWRITE SUBSETP-MEMBER . 1))
     (2 2 (:REWRITE MEMBER-WHEN-ATOM))
     (2 2 (:REWRITE INTERSECTP-MEMBER . 3))
     (2 2 (:REWRITE INTERSECTP-MEMBER . 2))
     (1 1 (:REWRITE DUPLICITY-WHEN-NOT-CONSP))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(COMPARABLE-MERGESORT-IS-IDENTITY-UNDER-SET-EQUIV-LEMMA-1
     (158 8 (:DEFINITION MEMBER-EQUAL))
     (94 3
         (:REWRITE DUPLICITY-WHEN-NON-MEMBER-EQUAL))
     (60 8 (:REWRITE CONSP-OF-TAKE))
     (53 16 (:REWRITE SUBSETP-MEMBER . 2))
     (52 10 (:REWRITE SUBSETP-TRANS))
     (50 50
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (40 8 (:DEFINITION LEN))
     (38 32 (:REWRITE DEFAULT-<-2))
     (37 32 (:REWRITE DEFAULT-<-1))
     (36 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (32 32
         (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGESORT))
     (32 18 (:REWRITE DEFAULT-CDR))
     (31 5
         (:REWRITE DUPLICITY-WHEN-MEMBER-EQUAL))
     (26 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (24 16 (:REWRITE DEFAULT-+-2))
     (20 8 (:REWRITE MEMBER-WHEN-ATOM))
     (18 6 (:REWRITE <-0-+-NEGATIVE-1))
     (18 2 (:REWRITE CAR-OF-TAKE))
     (18 2 (:DEFINITION NTH))
     (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (16 16 (:REWRITE SUBSETP-MEMBER . 1))
     (16 16 (:REWRITE DEFAULT-+-1))
     (15 9 (:REWRITE DEFAULT-CAR))
     (12 12
         (:REWRITE CONSP-OF-COMPARABLE-MERGESORT))
     (12 4
         (:REWRITE COMPARABLE-MERGESORT-EQUALS-COMPARABLE-INSERTSORT))
     (8 8
        (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (8 8 (:REWRITE SUBSETP-MEMBER . 4))
     (8 8 (:REWRITE SUBSETP-MEMBER . 3))
     (8 8 (:REWRITE INTERSECTP-MEMBER . 3))
     (8 8 (:REWRITE INTERSECTP-MEMBER . 2))
     (6 2 (:REWRITE FOLD-CONSTS-IN-+))
     (4 2 (:REWRITE TAKE-UNDER-IFF))
     (3 3 (:REWRITE DUPLICITY-WHEN-NOT-CONSP)))
(COMPARABLE-MERGESORT-IS-IDENTITY-UNDER-SET-EQUIV
     (10 2 (:DEFINITION LEN))
     (9 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (9 3
        (:REWRITE COMPARABLE-MERGESORT-EQUALS-COMPARABLE-INSERTSORT))
     (6 6
        (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (5 4 (:REWRITE SUBSETP-TRANS))
     (4 4
        (:TYPE-PRESCRIPTION TRUE-LISTP-OF-COMPARABLE-MERGESORT))
     (4 2 (:REWRITE DEFAULT-<-1))
     (4 2 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE CONSP-OF-COMPARABLE-MERGESORT)))
(COMMON-SORT-FOR-PERMS-LEMMA-1
     (1063 279 (:REWRITE COMPARE<-TOTAL-NECC))
     (882 49 (:DEFINITION COMPARE<-TOTAL))
     (621 278
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (314 55
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (298 272 (:REWRITE COMPARE<-TRANSITIVE))
     (196 196 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (84 84 (:REWRITE DEFAULT-CDR))
     (38 22 (:REWRITE SUBSETP-MEMBER . 3))
     (25 25
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (22 22 (:REWRITE SUBSETP-MEMBER . 4))
     (22 22 (:REWRITE SUBSETP-MEMBER . 2))
     (22 22 (:REWRITE SUBSETP-MEMBER . 1))
     (22 22 (:REWRITE INTERSECTP-MEMBER . 3))
     (22 22 (:REWRITE INTERSECTP-MEMBER . 2))
     (5 5 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (3 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (3 3 (:REWRITE SUBSETP-TRANS2))
     (3 3 (:REWRITE SUBSETP-TRANS))
     (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT)))
(COMMON-SORT-FOR-PERMS-LEMMA-2
     (9142 2454 (:REWRITE COMPARE<-TOTAL-NECC))
     (7524 418 (:DEFINITION COMPARE<-TOTAL))
     (2012 1291 (:REWRITE DEFAULT-CDR))
     (2002 40 (:REWRITE SUBSETP-OF-CONS))
     (1672 1672
           (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (1262 126 (:REWRITE SECOND-OF-TAKE))
     (1240 20 (:REWRITE SUBSETP-OF-TAKE))
     (1238 1016 (:REWRITE DEFAULT-<-1))
     (1076 1016 (:REWRITE DEFAULT-<-2))
     (890 417
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (690 230 (:REWRITE <-+-NEGATIVE-0-1))
     (681 437
          (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (505 50
          (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (304 32 (:REWRITE THIRD-OF-TAKE))
     (290 290 (:REWRITE SUBSETP-TRANS2))
     (290 290 (:REWRITE SUBSETP-TRANS))
     (280 280 (:TYPE-PRESCRIPTION LEN))
     (226 226 (:REWRITE SUBSETP-MEMBER . 2))
     (214 174 (:REWRITE DEFAULT-+-2))
     (200 40 (:DEFINITION LEN))
     (174 174 (:REWRITE DEFAULT-+-1))
     (125 125 (:REWRITE SUBSETP-MEMBER . 4))
     (125 125 (:REWRITE INTERSECTP-MEMBER . 3))
     (125 125 (:REWRITE INTERSECTP-MEMBER . 2))
     (109 9 (:REWRITE SUBSETP-CAR-MEMBER))
     (57 7 (:DEFINITION ATOM)))
(COMMON-SORT-FOR-PERMS-LEMMA-3
     (1297 33 (:DEFINITION MEMBER-EQUAL))
     (722 67
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (467 68 (:REWRITE SUBSETP-MEMBER . 1))
     (410 38
          (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (378 117 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (358 37 (:REWRITE SUBSETP-CAR-MEMBER))
     (317 67
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (311 180 (:REWRITE DEFAULT-CDR))
     (282 52 (:REWRITE ZP-OPEN))
     (174 66
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (164 164
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (152 116 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (138 46 (:REWRITE <-0-+-NEGATIVE-1))
     (133 133
          (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (123 113 (:REWRITE DEFAULT-<-2))
     (120 120 (:REWRITE SUBSETP-TRANS2))
     (120 120 (:REWRITE SUBSETP-TRANS))
     (115 113 (:REWRITE DEFAULT-<-1))
     (80 11 (:REWRITE CAR-OF-TAKE))
     (68 68 (:REWRITE SUBSETP-MEMBER . 2))
     (67 67 (:REWRITE SUBSETP-MEMBER . 4))
     (67 67 (:REWRITE INTERSECTP-MEMBER . 3))
     (67 67 (:REWRITE INTERSECTP-MEMBER . 2))
     (65 62 (:REWRITE DEFAULT-CAR))
     (64 45 (:REWRITE DEFAULT-+-2))
     (45 45 (:REWRITE DEFAULT-+-1))
     (44 1 (:REWRITE SUBSETP-OF-CONS))
     (27 27
         (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-DUPLICITY-BADGUY1))
     (27 9 (:REWRITE FOLD-CONSTS-IN-+))
     (26 26
         (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-HIGH-DUPLICITY))
     (20 1 (:REWRITE SUBSETP-CONS-2))
     (18 3 (:REWRITE COMPARE<-TOTAL-NECC))
     (16 1 (:DEFINITION COMPARE<-TOTAL))
     (7 3
        (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (5 5 (:TYPE-PRESCRIPTION TYPE-OF-COMPARE<))
     (4 4
        (:TYPE-PRESCRIPTION COMPARE<-NEGATION-TRANSITIVE))
     (3 3 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (3 3 (:REWRITE COMPARE<-TRANSITIVE))
     (2 1 (:REWRITE TAKE-UNDER-IFF))
     (1 1 (:REWRITE CDR-CONS)))
(COMMON-SORT-FOR-PERMS-LEMMA-5
     (1475 292 (:REWRITE COMPARE<-TOTAL-NECC))
     (1428 292
           (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (1316 43 (:DEFINITION COMPARE<-TOTAL))
     (900 18
          (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (662 40
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (625 32
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (503 290 (:REWRITE COMPARE<-TRANSITIVE))
     (414 18 (:DEFINITION MEMBER-EQUAL))
     (271 20 (:REWRITE COMPARE<-STRICT-NECC))
     (252 36 (:REWRITE SUBSETP-CAR-MEMBER))
     (219 219 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (143 117 (:REWRITE DEFAULT-CDR))
     (112 40
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (92 32
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (77 77
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (72 61 (:REWRITE DEFAULT-CAR))
     (52 37
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (40 40 (:REWRITE SUBSETP-MEMBER . 4))
     (40 40 (:REWRITE SUBSETP-MEMBER . 3))
     (40 40 (:REWRITE SUBSETP-MEMBER . 2))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 3))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 2))
     (37 37 (:REWRITE SUBSETP-TRANS2))
     (37 37 (:REWRITE SUBSETP-TRANS))
     (36 36 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (36 36 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (30 3 (:REWRITE ZP-OPEN))
     (22 22
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (16 16 (:REWRITE DEFAULT-+-1))
     (13 3 (:REWRITE CAR-OF-TAKE))
     (12 3 (:REWRITE <-0-+-NEGATIVE-1))
     (10 8 (:REWRITE DEFAULT-<-1))
     (9 9
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (3 1 (:REWRITE FOLD-CONSTS-IN-+)))
(COMMON-SORT-FOR-PERMS-LEMMA-6
     (100 2 (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (70 18 (:REWRITE COMPARE<-TOTAL-NECC))
     (59 18
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (56 4 (:DEFINITION COMPARE<-TOTAL))
     (46 2 (:DEFINITION MEMBER-EQUAL))
     (32 17 (:REWRITE COMPARE<-TRANSITIVE))
     (30 5
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (28 4 (:REWRITE SUBSETP-CAR-MEMBER))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 1 (:DEFINITION NTH))
     (12 12 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (10 10
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (10 5
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (8 8
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (7 7 (:REWRITE DEFAULT-CAR))
     (7 1 (:DEFINITION LEN))
     (6 1 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE SUBSETP-TRANS2))
     (5 5 (:REWRITE SUBSETP-TRANS))
     (5 5 (:REWRITE SUBSETP-MEMBER . 4))
     (5 5 (:REWRITE INTERSECTP-MEMBER . 3))
     (5 5 (:REWRITE INTERSECTP-MEMBER . 2))
     (5 5
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (5 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
     (4 4 (:REWRITE MEMBER-WHEN-ATOM))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 1 (:REWRITE FOLD-CONSTS-IN-+))
     (3 1 (:REWRITE <-0-+-NEGATIVE-1))
     (2 2
        (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (2 2
        (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (2 1 (:REWRITE COMPARE<-STRICT-NECC))
     (2 1
        (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (1 1
        (:REWRITE COMPARE-TRANSITIVE-IMPLIES)))
(COMMON-SORT-FOR-PERMS-LEMMA-4
     (2403 570
           (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (2256 570 (:REWRITE COMPARE<-TOTAL-NECC))
     (1844 98 (:DEFINITION COMPARE<-TOTAL))
     (1009 546 (:REWRITE COMPARE<-TRANSITIVE))
     (950 19
          (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (498 20 (:DEFINITION MEMBER-EQUAL))
     (354 354 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (278 40
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (266 38 (:REWRITE SUBSETP-CAR-MEMBER))
     (148 128 (:REWRITE DEFAULT-CDR))
     (135 9 (:DEFINITION NTH))
     (128 49
          (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (102 40
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (80 15 (:REWRITE ZP-OPEN))
     (76 76 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (70 67 (:REWRITE DEFAULT-CAR))
     (56 40 (:REWRITE MEMBER-WHEN-ATOM))
     (56 40
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (46 5 (:REWRITE CONSP-OF-TAKE))
     (40 40 (:REWRITE SUBSETP-MEMBER . 4))
     (40 40 (:REWRITE SUBSETP-MEMBER . 3))
     (40 40 (:REWRITE SUBSETP-MEMBER . 2))
     (40 40 (:REWRITE SUBSETP-MEMBER . 1))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 3))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 2))
     (39 13 (:REWRITE <-0-+-NEGATIVE-1))
     (38 38 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (38 38 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (38 38 (:REWRITE SUBSETP-TRANS2))
     (38 38 (:REWRITE SUBSETP-TRANS))
     (30 28 (:REWRITE DEFAULT-+-2))
     (29 29
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (28 28 (:REWRITE DEFAULT-+-1))
     (27 9 (:REWRITE FOLD-CONSTS-IN-+))
     (23 23
         (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (22 20 (:REWRITE DEFAULT-<-1))
     (20 20 (:REWRITE DEFAULT-<-2))
     (14 2 (:DEFINITION LEN))
     (12 1 (:REWRITE CAR-OF-TAKE))
     (6 3 (:REWRITE SET-EQUIV-ASYM))
     (5 1 (:DEFINITION NFIX))
     (4 4
        (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (3 1 (:REWRITE <-+-NEGATIVE-0-1))
     (1 1 (:TYPE-PRESCRIPTION NFIX)))
(COMMON-SORT-FOR-PERMS-LEMMA-8
     (887 169 (:REWRITE COMPARE<-TOTAL-NECC))
     (824 169
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (806 16 (:DEFINITION COMPARE<-TOTAL))
     (600 12
          (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (463 32
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (443 28
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (276 12 (:DEFINITION MEMBER-EQUAL))
     (244 167 (:REWRITE COMPARE<-TRANSITIVE))
     (168 24 (:REWRITE SUBSETP-CAR-MEMBER))
     (120 120 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (109 20 (:REWRITE COMPARE<-STRICT-NECC))
     (107 81 (:REWRITE DEFAULT-CDR))
     (92 32
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (88 28
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (54 43 (:REWRITE DEFAULT-CAR))
     (53 53
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (40 25
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (31 4 (:REWRITE ZP-OPEN))
     (28 28 (:REWRITE SUBSETP-MEMBER . 4))
     (28 28 (:REWRITE SUBSETP-MEMBER . 3))
     (28 28 (:REWRITE SUBSETP-MEMBER . 2))
     (28 28 (:REWRITE INTERSECTP-MEMBER . 3))
     (28 28 (:REWRITE INTERSECTP-MEMBER . 2))
     (25 25 (:REWRITE SUBSETP-TRANS2))
     (25 25 (:REWRITE SUBSETP-TRANS))
     (24 24 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (24 24 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (22 22
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (13 3 (:REWRITE CAR-OF-TAKE))
     (13 1
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-5))
     (12 12 (:REWRITE DEFAULT-+-1))
     (12 3 (:REWRITE <-0-+-NEGATIVE-1))
     (10 8 (:REWRITE DEFAULT-<-1))
     (9 9
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 1
        (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (3 1 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:TYPE-PRESCRIPTION ZP)))
(COMMON-SORT-FOR-PERMS-LEMMA-9
     (100 2 (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (46 2 (:DEFINITION MEMBER-EQUAL))
     (30 5
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (28 4 (:REWRITE SUBSETP-CAR-MEMBER))
     (26 9
         (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (22 9 (:REWRITE COMPARE<-TOTAL-NECC))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 1 (:DEFINITION NTH))
     (14 1 (:DEFINITION COMPARE<-TOTAL))
     (13 8 (:REWRITE COMPARE<-TRANSITIVE))
     (13 1
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (10 10
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (10 5
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (8 8
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (7 7 (:REWRITE DEFAULT-CAR))
     (7 1 (:DEFINITION LEN))
     (6 1 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE SUBSETP-TRANS2))
     (5 5 (:REWRITE SUBSETP-TRANS))
     (5 5 (:REWRITE SUBSETP-MEMBER . 4))
     (5 5 (:REWRITE INTERSECTP-MEMBER . 3))
     (5 5 (:REWRITE INTERSECTP-MEMBER . 2))
     (5 5
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (5 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
     (4 4 (:REWRITE MEMBER-WHEN-ATOM))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 1 (:REWRITE FOLD-CONSTS-IN-+))
     (3 1 (:REWRITE <-0-+-NEGATIVE-1))
     (2 2
        (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (2 2
        (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (2 1 (:REWRITE COMPARE<-STRICT-NECC))
     (2 1
        (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (1 1
        (:REWRITE COMPARE-TRANSITIVE-IMPLIES)))
(COMMON-SORT-FOR-PERMS-LEMMA-10
     (274 62 (:REWRITE COMPARE<-TOTAL-NECC))
     (264 62
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (250 5 (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (236 6 (:DEFINITION COMPARE<-TOTAL))
     (159 13
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (115 5 (:DEFINITION MEMBER-EQUAL))
     (81 59 (:REWRITE COMPARE<-TRANSITIVE))
     (75 11
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (70 10 (:REWRITE SUBSETP-CAR-MEMBER))
     (45 3 (:DEFINITION NTH))
     (41 9 (:REWRITE COMPARE<-STRICT-NECC))
     (38 35 (:REWRITE DEFAULT-CDR))
     (36 36 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (33 13
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (32 1
         (:REWRITE DUPLICITY-WHEN-NON-MEMBER-EQUAL))
     (28 11
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (22 22
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (18 18 (:REWRITE DEFAULT-CAR))
     (14 14
         (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (14 11
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (14 2
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (10 10 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (10 10 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (10 10 (:REWRITE SUBSETP-TRANS2))
     (10 10 (:REWRITE SUBSETP-TRANS))
     (10 10 (:REWRITE SUBSETP-MEMBER . 4))
     (10 10 (:REWRITE SUBSETP-MEMBER . 3))
     (10 10 (:REWRITE SUBSETP-MEMBER . 2))
     (10 10 (:REWRITE SUBSETP-MEMBER . 1))
     (10 10 (:REWRITE MEMBER-WHEN-ATOM))
     (10 10 (:REWRITE INTERSECTP-MEMBER . 3))
     (10 10 (:REWRITE INTERSECTP-MEMBER . 2))
     (9 3 (:REWRITE FOLD-CONSTS-IN-+))
     (9 3 (:REWRITE <-0-+-NEGATIVE-1))
     (8 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (7 1 (:DEFINITION LEN))
     (6 6
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (6 6
        (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (5 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 1 (:REWRITE DUPLICITY-WHEN-NOT-CONSP)))
(COMMON-SORT-FOR-PERMS-LEMMA-7
     (950 19
          (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (898 223
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (758 223 (:REWRITE COMPARE<-TOTAL-NECC))
     (598 15 (:DEFINITION COMPARE<-TOTAL))
     (564 20 (:DEFINITION MEMBER-EQUAL))
     (278 40
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (273 200 (:REWRITE COMPARE<-TRANSITIVE))
     (266 38 (:REWRITE SUBSETP-CAR-MEMBER))
     (148 128 (:REWRITE DEFAULT-CDR))
     (135 9 (:DEFINITION NTH))
     (113 1
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-5))
     (102 40
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (99 47
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (93 93 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (83 2
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (80 15 (:REWRITE ZP-OPEN))
     (76 76 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (70 67 (:REWRITE DEFAULT-CAR))
     (56 40 (:REWRITE MEMBER-WHEN-ATOM))
     (56 40
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (46 5 (:REWRITE CONSP-OF-TAKE))
     (40 40 (:REWRITE SUBSETP-MEMBER . 4))
     (40 40 (:REWRITE SUBSETP-MEMBER . 3))
     (40 40 (:REWRITE SUBSETP-MEMBER . 2))
     (40 40 (:REWRITE SUBSETP-MEMBER . 1))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 3))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 2))
     (39 13 (:REWRITE <-0-+-NEGATIVE-1))
     (38 38 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (38 38 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (38 38 (:REWRITE SUBSETP-TRANS2))
     (38 38 (:REWRITE SUBSETP-TRANS))
     (30 28 (:REWRITE DEFAULT-+-2))
     (29 29
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (28 28 (:REWRITE DEFAULT-+-1))
     (27 9 (:REWRITE FOLD-CONSTS-IN-+))
     (23 23
         (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (22 20 (:REWRITE DEFAULT-<-1))
     (20 20 (:REWRITE DEFAULT-<-2))
     (14 2 (:DEFINITION LEN))
     (12 1 (:REWRITE CAR-OF-TAKE))
     (5 1 (:DEFINITION NFIX))
     (4 4
        (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (3 1 (:REWRITE <-+-NEGATIVE-0-1))
     (1 1 (:TYPE-PRESCRIPTION NFIX)))
(COMMON-SORT-FOR-PERMS-LEMMA-12
     (2718 452
           (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (2515 452 (:REWRITE COMPARE<-TOTAL-NECC))
     (2284 62 (:DEFINITION COMPARE<-TOTAL))
     (1121 28
           (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (837 101
          (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (689 101
          (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (600 12
          (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (519 48 (:REWRITE COMPARE<-STRICT-NECC))
     (450 450 (:REWRITE COMPARE<-TRANSITIVE))
     (345 345 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (276 12 (:DEFINITION MEMBER-EQUAL))
     (168 24 (:REWRITE SUBSETP-CAR-MEMBER))
     (107 81 (:REWRITE DEFAULT-CDR))
     (91 1
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-8))
     (91 1
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-5))
     (88 28
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (54 43 (:REWRITE DEFAULT-CAR))
     (53 53
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (40 25
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (31 4 (:REWRITE ZP-OPEN))
     (28 28 (:REWRITE SUBSETP-MEMBER . 4))
     (28 28 (:REWRITE SUBSETP-MEMBER . 3))
     (28 28 (:REWRITE SUBSETP-MEMBER . 2))
     (28 28 (:REWRITE INTERSECTP-MEMBER . 3))
     (28 28 (:REWRITE INTERSECTP-MEMBER . 2))
     (25 25 (:REWRITE SUBSETP-TRANS2))
     (25 25 (:REWRITE SUBSETP-TRANS))
     (24 24 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (24 24 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (22 22
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (13 3 (:REWRITE CAR-OF-TAKE))
     (12 12 (:REWRITE DEFAULT-+-1))
     (12 3 (:REWRITE <-0-+-NEGATIVE-1))
     (10 8 (:REWRITE DEFAULT-<-1))
     (9 9
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 1
        (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (3 1 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:TYPE-PRESCRIPTION ZP)))
(COMMON-SORT-FOR-PERMS-LEMMA-13
     (283 56
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (199 56 (:REWRITE COMPARE<-TOTAL-NECC))
     (154 11 (:DEFINITION COMPARE<-TOTAL))
     (100 2 (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (91 1
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-9))
     (91 1
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (69 9
         (:REWRITE COMPARE<-REVERSE-WHEN-STRICT))
     (69 9 (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (55 55 (:REWRITE COMPARE<-TRANSITIVE))
     (46 2 (:DEFINITION MEMBER-EQUAL))
     (33 33 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (30 5
         (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (28 4 (:REWRITE SUBSETP-CAR-MEMBER))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 1 (:DEFINITION NTH))
     (10 10
         (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (10 5
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (8 8
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (8 4 (:REWRITE COMPARE<-STRICT-NECC))
     (7 7 (:REWRITE DEFAULT-CAR))
     (7 1 (:DEFINITION LEN))
     (6 1 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE SUBSETP-TRANS2))
     (5 5 (:REWRITE SUBSETP-TRANS))
     (5 5 (:REWRITE SUBSETP-MEMBER . 4))
     (5 5 (:REWRITE INTERSECTP-MEMBER . 3))
     (5 5 (:REWRITE INTERSECTP-MEMBER . 2))
     (5 5
        (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (5 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
     (4 4 (:REWRITE MEMBER-WHEN-ATOM))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 1 (:REWRITE FOLD-CONSTS-IN-+))
     (3 1 (:REWRITE <-0-+-NEGATIVE-1))
     (2 2
        (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (2 2
        (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT)))
(COMMON-SORT-FOR-PERMS-LEMMA-11
     (5654 1135
           (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (4790 1135 (:REWRITE COMPARE<-TOTAL-NECC))
     (3995 194 (:DEFINITION COMPARE<-TOTAL))
     (1662 221
           (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (1109 1109 (:REWRITE COMPARE<-TRANSITIVE))
     (950 19
          (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (790 20 (:DEFINITION MEMBER-EQUAL))
     (728 728 (:TYPE-PRESCRIPTION COMPARE<-TOTAL))
     (387 2
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-6))
     (278 40
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (266 38 (:REWRITE SUBSETP-CAR-MEMBER))
     (148 128 (:REWRITE DEFAULT-CDR))
     (135 9 (:DEFINITION NTH))
     (113 1
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-5))
     (102 40
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (80 15 (:REWRITE ZP-OPEN))
     (76 76 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (70 67 (:REWRITE DEFAULT-CAR))
     (56 40 (:REWRITE MEMBER-WHEN-ATOM))
     (56 40
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (46 5 (:REWRITE CONSP-OF-TAKE))
     (40 40 (:REWRITE SUBSETP-MEMBER . 4))
     (40 40 (:REWRITE SUBSETP-MEMBER . 3))
     (40 40 (:REWRITE SUBSETP-MEMBER . 2))
     (40 40 (:REWRITE SUBSETP-MEMBER . 1))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 3))
     (40 40 (:REWRITE INTERSECTP-MEMBER . 2))
     (39 13 (:REWRITE <-0-+-NEGATIVE-1))
     (38 38 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (38 38 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (38 38 (:REWRITE SUBSETP-TRANS2))
     (38 38 (:REWRITE SUBSETP-TRANS))
     (30 28 (:REWRITE DEFAULT-+-2))
     (29 29
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (28 28 (:REWRITE DEFAULT-+-1))
     (27 9 (:REWRITE FOLD-CONSTS-IN-+))
     (23 23
         (:TYPE-PRESCRIPTION COMPARABLE-INSERTSORT))
     (22 20 (:REWRITE DEFAULT-<-1))
     (20 20 (:REWRITE DEFAULT-<-2))
     (14 2 (:DEFINITION LEN))
     (12 1 (:REWRITE CAR-OF-TAKE))
     (5 1 (:DEFINITION NFIX))
     (4 4
        (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
     (3 1 (:REWRITE <-+-NEGATIVE-0-1))
     (1 1 (:TYPE-PRESCRIPTION NFIX)))
(COMMON-SORT-FOR-PERMS-LEMMA-14
     (14000 280
            (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (13976 3686
            (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (6440 280 (:DEFINITION MEMBER-EQUAL))
     (5048 1240
           (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (4574 3611 (:REWRITE COMPARE<-TRANSITIVE))
     (4158 162 (:DEFINITION BINARY-APPEND))
     (3920 560 (:REWRITE SUBSETP-CAR-MEMBER))
     (3518 2258 (:REWRITE DEFAULT-CDR))
     (3360 560
           (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (2646 1368 (:REWRITE DEFAULT-CAR))
     (1323 324 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (1120 1120 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1120 1120
           (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (1120 560
           (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (1108 1034 (:REWRITE DEFAULT-<-1))
     (1043 1034 (:REWRITE DEFAULT-<-2))
     (972 108 (:REWRITE SECOND-OF-TAKE))
     (615 529 (:REWRITE DEFAULT-+-2))
     (602 86 (:DEFINITION LEN))
     (560 560 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (560 560 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (560 560 (:REWRITE SUBSETP-TRANS2))
     (560 560 (:REWRITE SUBSETP-TRANS))
     (560 560 (:REWRITE SUBSETP-MEMBER . 4))
     (560 560 (:REWRITE SUBSETP-MEMBER . 3))
     (560 560 (:REWRITE SUBSETP-MEMBER . 2))
     (560 560 (:REWRITE SUBSETP-MEMBER . 1))
     (560 560 (:REWRITE MEMBER-WHEN-ATOM))
     (560 560 (:REWRITE INTERSECTP-MEMBER . 3))
     (560 560 (:REWRITE INTERSECTP-MEMBER . 2))
     (560 560
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (529 529 (:REWRITE DEFAULT-+-1))
     (280 280 (:TYPE-PRESCRIPTION MEMBER-EQUAL)))
(COMMON-SORT-FOR-PERMS
     (2050 41
           (:DEFINITION REMOVE-DUPLICATES-EQUAL))
     (943 41 (:DEFINITION MEMBER-EQUAL))
     (574 82 (:REWRITE SUBSETP-CAR-MEMBER))
     (492 82
          (:REWRITE COMMON-SORT-FOR-PERMS-LEMMA-1))
     (272 272 (:REWRITE DEFAULT-CDR))
     (164 164 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (164 164
          (:TYPE-PRESCRIPTION COMPARABLE-ORDEREDP))
     (164 82
          (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP-OF-CDR))
     (133 81
          (:REWRITE COMPARE-NEGATION-TRANSITIVE-IMPLIES))
     (123 123 (:REWRITE DEFAULT-CAR))
     (107 67 (:REWRITE COMPARE<-TRANSITIVE))
     (82 82 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (82 82 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (82 82 (:REWRITE SUBSETP-TRANS2))
     (82 82 (:REWRITE SUBSETP-TRANS))
     (82 82 (:REWRITE SUBSETP-MEMBER . 4))
     (82 82 (:REWRITE SUBSETP-MEMBER . 3))
     (82 82 (:REWRITE SUBSETP-MEMBER . 2))
     (82 82 (:REWRITE SUBSETP-MEMBER . 1))
     (82 82 (:REWRITE MEMBER-WHEN-ATOM))
     (82 82 (:REWRITE INTERSECTP-MEMBER . 3))
     (82 82 (:REWRITE INTERSECTP-MEMBER . 2))
     (82 82
         (:REWRITE COMPARABLE-ORDEREDP-WHEN-NOT-CONSP))
     (52 26 (:REWRITE DEFAULT-+-2))
     (41 41 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (30 20
         (:REWRITE COMPARE-TRANSITIVE-IMPLIES))
     (26 26 (:REWRITE DEFAULT-+-1))
     (4 2 (:REWRITE DEFAULT-<-1))
     (3 2 (:REWRITE DEFAULT-<-2)))
