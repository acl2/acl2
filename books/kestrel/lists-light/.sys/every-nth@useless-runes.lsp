(EVERY-NTH-EXEC-AUX
 (16 9 (:REWRITE DEFAULT-+-2))
 (10 9 (:REWRITE DEFAULT-+-1))
 (10 6 (:REWRITE DEFAULT-<-1))
 (7 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(EVERY-NTH-EXEC)
(EVERY-NTH
 (16 9 (:REWRITE DEFAULT-+-2))
 (10 9 (:REWRITE DEFAULT-+-1))
 (10 6 (:REWRITE DEFAULT-<-1))
 (7 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-CDR))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(EVERY-NTH-EXEC-AUX-HELPER
 (667 23 (:REWRITE CDR-OF-REVAPPEND))
 (644 23 (:DEFINITION BUTLAST))
 (366 20 (:REWRITE NTHCDR-OF-NTHCDR))
 (276 23 (:DEFINITION TAKE))
 (260 217 (:REWRITE DEFAULT-+-2))
 (250 20 (:REWRITE CONSP-OF-NTHCDR))
 (217 217 (:REWRITE DEFAULT-+-1))
 (215 43 (:DEFINITION LEN))
 (211 168 (:REWRITE DEFAULT-<-2))
 (210 174 (:REWRITE DEFAULT-CDR))
 (200 60 (:DEFINITION NFIX))
 (184 20 (:REWRITE CAR-OF-NTHCDR))
 (168 168 (:REWRITE DEFAULT-<-1))
 (164 20 (:DEFINITION NTH))
 (158 99 (:REWRITE DEFAULT-CAR))
 (138 23 (:REWRITE CAR-OF-REVAPPEND))
 (134 35 (:REWRITE ZP-OPEN))
 (119 53 (:REWRITE FOLD-CONSTS-IN-+))
 (116 52 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (75 25 (:REWRITE COMMUTATIVITY-OF-+))
 (69 23 (:DEFINITION LAST))
 (60 20 (:REWRITE <-OF-+-OF---AND-0-ARG1))
 (60 10 (:REWRITE COMMUTATIVITY-2-OF-+))
 (52 52 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (52 52 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (44 22 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (23 23 (:TYPE-PRESCRIPTION LAST))
 (23 23 (:REWRITE CONSP-OF-REVAPPEND))
 (16 16 (:TYPE-PRESCRIPTION POSP))
 )
(EVERY-NTH
 (24 2 (:REWRITE NTHCDR-OF-NTHCDR))
 (24 2 (:REWRITE CONSP-OF-NTHCDR))
 (18 6 (:DEFINITION NFIX))
 (11 9 (:REWRITE DEFAULT-<-2))
 (10 2 (:REWRITE CAR-OF-NTHCDR))
 (10 2 (:DEFINITION LEN))
 (9 9 (:REWRITE DEFAULT-<-1))
 (8 6 (:REWRITE DEFAULT-+-2))
 (8 2 (:DEFINITION NTH))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (5 5 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (5 5 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (2 1 (:DEFINITION TRUE-LISTP))
 )
(CONSP-OF-EVERY-NTH
 (10 5 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (7 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 1 (:DEFINITION LEN))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (2 2 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(IND
 (16 9 (:REWRITE DEFAULT-+-2))
 (10 9 (:REWRITE DEFAULT-+-1))
 (10 6 (:REWRITE DEFAULT-<-1))
 (7 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(NTH-OF-EVERY-NTH
 (112 100 (:REWRITE DEFAULT-<-2))
 (109 22 (:REWRITE DEFAULT-CAR))
 (105 21 (:DEFINITION LEN))
 (104 38 (:REWRITE DEFAULT-CDR))
 (100 100 (:REWRITE DEFAULT-<-1))
 (84 7 (:REWRITE NTHCDR-OF-NTHCDR))
 (80 80 (:REWRITE DEFAULT-*-2))
 (80 80 (:REWRITE DEFAULT-*-1))
 (79 58 (:REWRITE DEFAULT-+-2))
 (58 58 (:REWRITE DEFAULT-+-1))
 (51 19 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (44 11 (:REWRITE ZP-OPEN))
 (42 21 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (38 38 (:LINEAR <-OF-*-AND-*-LINEAR))
 (35 7 (:REWRITE CAR-OF-NTHCDR))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 16 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (16 16 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (16 16 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (14 2 (:REWRITE <-OF-0-AND-*))
 (13 5 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 )
(NTH-WHEN-REMAINDER-KNOWN
 (279 6 (:DEFINITION NTH))
 (267 3 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (147 6 (:REWRITE ZP-OPEN))
 (92 4 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (88 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (84 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (78 18 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (72 4 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (66 30 (:REWRITE DEFAULT-<-2))
 (48 18 (:REWRITE MOD-WHEN-<))
 (43 19 (:REWRITE DEFAULT-*-2))
 (41 14 (:REWRITE DEFAULT-+-2))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (33 30 (:REWRITE DEFAULT-<-1))
 (31 14 (:REWRITE DEFAULT-+-1))
 (27 19 (:REWRITE DEFAULT-*-1))
 (18 18 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (18 18 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (18 18 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (18 18 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (18 18 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (18 18 (:REWRITE MOD-WHEN-<-OF-0))
 (15 15 (:REWRITE INTEGERP-OF-*))
 (15 15 (:REWRITE DEFAULT-UNARY-/))
 (9 3 (:REWRITE FLOOR-WHEN-<))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (3 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (3 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (3 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 )
(LEN-OF-EVERY-NTH
 (77 61 (:REWRITE DEFAULT-<-2))
 (77 16 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (69 40 (:REWRITE DEFAULT-+-2))
 (68 47 (:REWRITE DEFAULT-*-2))
 (66 61 (:REWRITE DEFAULT-<-1))
 (53 47 (:REWRITE DEFAULT-*-1))
 (41 40 (:REWRITE DEFAULT-+-1))
 (36 3 (:REWRITE NTHCDR-OF-NTHCDR))
 (29 29 (:REWRITE DEFAULT-UNARY-/))
 (29 16 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (26 13 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (16 16 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (16 16 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (16 16 (:REWRITE INTEGERP-OF-*))
 (16 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (16 2 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (15 3 (:REWRITE CAR-OF-NTHCDR))
 (13 13 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 3 (:DEFINITION NTH))
 (8 8 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (8 8 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (8 8 (:LINEAR CEILING-UPPER-BOUND-WHEN-<-CONSTANT-LINEAR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*-LINEAR))
 (4 2 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
