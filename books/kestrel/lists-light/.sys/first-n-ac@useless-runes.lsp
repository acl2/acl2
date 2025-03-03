(CONSP-OF-FIRST-N-AC
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(FIRST-N-AC-OF-CONS
 (10 4 (:REWRITE ZP-OPEN))
 (10 2 (:REWRITE REVAPPEND-OF-CONS))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE APPEND-OF-CONS-ARG1))
 )
(FIRST-N-AC-OF-APPEND-ARG3
 (362 2 (:REWRITE REVAPPEND-OF-CONS))
 (230 2 (:REWRITE APPEND-ASSOCIATIVE))
 (180 32 (:DEFINITION REVAPPEND))
 (168 14 (:DEFINITION TAKE))
 (138 40 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (103 103 (:REWRITE DEFAULT-CDR))
 (95 81 (:REWRITE DEFAULT-+-2))
 (89 75 (:REWRITE DEFAULT-CAR))
 (81 81 (:REWRITE DEFAULT-+-1))
 (70 22 (:REWRITE ZP-OPEN))
 (70 14 (:DEFINITION LEN))
 (48 16 (:REWRITE FOLD-CONSTS-IN-+))
 (44 30 (:REWRITE DEFAULT-<-2))
 (42 42 (:TYPE-PRESCRIPTION TAKE))
 (42 14 (:DEFINITION LAST))
 (30 30 (:REWRITE DEFAULT-<-1))
 (14 14 (:TYPE-PRESCRIPTION LAST))
 )
(FIRST-N-AC-OF-CONS-ARG3)
(FIRST-N-AC-NORMALIZE-AC
 (20 20 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE REVAPPEND-NORMALIZE-ACC))
 (15 15 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 )
(LEN-OF-FIRST-N-AC
 (108 61 (:REWRITE DEFAULT-+-2))
 (76 61 (:REWRITE DEFAULT-+-1))
 (50 31 (:REWRITE DEFAULT-CDR))
 (40 12 (:REWRITE CONSP-OF-FIRST-N-AC))
 (18 17 (:REWRITE DEFAULT-<-1))
 (18 6 (:DEFINITION POSP))
 (17 17 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION REVAPPEND))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(TRUE-LIST-FIX-OF-FIRST-N-AC
 (58 41 (:REWRITE DEFAULT-CDR))
 (57 38 (:REWRITE DEFAULT-CAR))
 (43 13 (:REWRITE ZP-OPEN))
 (38 36 (:REWRITE DEFAULT-+-2))
 (36 36 (:REWRITE DEFAULT-+-1))
 (30 10 (:REWRITE FOLD-CONSTS-IN-+))
 (24 2 (:DEFINITION TAKE))
 (20 6 (:REWRITE CONSP-OF-FIRST-N-AC))
 (19 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 (12 4 (:DEFINITION POSP))
 (10 2 (:DEFINITION LEN))
 (6 2 (:DEFINITION LAST))
 (2 2 (:TYPE-PRESCRIPTION LAST))
 )
(FIRST-N-AC-OF-0)
(FIRST-N-AC-IFF
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 )
(CAR-OF-FIRST-N-AC
 (27 27 (:REWRITE DEFAULT-CDR))
 (17 11 (:REWRITE ZP-OPEN))
 (13 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 (12 6 (:REWRITE CONSP-OF-FIRST-N-AC))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:DEFINITION POSP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(FIRST-N-AC-WHEN-NOT-INTEGERP-CHEAP)
(<=-OF-ACL2-COUNT-OF-FIRST-N-AC
 (563 283 (:REWRITE DEFAULT-+-2))
 (383 283 (:REWRITE DEFAULT-+-1))
 (243 1 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (203 7 (:REWRITE CDR-OF-REVAPPEND))
 (196 7 (:DEFINITION BUTLAST))
 (168 4 (:REWRITE CDR-OF-APPEND))
 (160 40 (:DEFINITION INTEGER-ABS))
 (160 20 (:DEFINITION LENGTH))
 (122 108 (:REWRITE DEFAULT-CDR))
 (109 87 (:REWRITE FOLD-CONSTS-IN-+))
 (88 70 (:REWRITE DEFAULT-<-1))
 (84 7 (:DEFINITION TAKE))
 (82 70 (:REWRITE DEFAULT-<-2))
 (76 63 (:REWRITE DEFAULT-CAR))
 (52 4 (:REWRITE CAR-OF-APPEND))
 (45 33 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (43 13 (:REWRITE ZP-OPEN))
 (42 7 (:REWRITE CAR-OF-REVAPPEND))
 (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (33 33 (:TYPE-PRESCRIPTION REVAPPEND))
 (30 9 (:DEFINITION LAST))
 (20 20 (:REWRITE DEFAULT-REALPART))
 (20 20 (:REWRITE DEFAULT-NUMERATOR))
 (20 20 (:REWRITE DEFAULT-IMAGPART))
 (20 20 (:REWRITE DEFAULT-DENOMINATOR))
 (20 20 (:REWRITE DEFAULT-COERCE-2))
 (20 20 (:REWRITE DEFAULT-COERCE-1))
 (19 19 (:REWRITE FIRST-N-AC-WHEN-NOT-INTEGERP-CHEAP))
 (16 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (15 4 (:REWRITE CONSP-OF-FIRST-N-AC))
 (14 2 (:REWRITE CAR-OF-FIRST-N-AC))
 (11 11 (:REWRITE CONSP-OF-REVAPPEND))
 (9 3 (:DEFINITION POSP))
 (8 8 (:TYPE-PRESCRIPTION LAST))
 (4 4 (:TYPE-PRESCRIPTION TAKE))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
