(BV-ARRAY-READ-SEGMENT
 (20 17 (:REWRITE DEFAULT-+-2))
 (20 17 (:REWRITE DEFAULT-+-1))
 (17 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 (17 17 (:REWRITE BOUND-WHEN-USB))
 (14 14 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 1 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (11 1 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE USE-ALL-NATP-2))
 (6 6 (:REWRITE USE-ALL-NATP))
 (6 6 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (6 6 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (2 1 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
 (2 1 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (1 1 (:REWRITE BV-ARRAYP-CONSTANT-OPENER))
 (1 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 )
(UNSIGNED-BYTE-LISTP-OF-BV-ARRAY-READ-SEGMENT
 (52 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (24 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (22 22 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (21 21 (:REWRITE DEFAULT-<-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE BOUND-WHEN-USB))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 8 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE USE-ALL-NATP-2))
 (8 8 (:REWRITE USE-ALL-NATP))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (8 8 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (3 3 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (3 3 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (3 3 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (3 3 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (3 3 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 )
(LEN-OF-BV-ARRAY-READ-SEGMENT
 (33 21 (:REWRITE DEFAULT-<-1))
 (24 4 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (23 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (22 11 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (21 21 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE BOUND-WHEN-USB))
 (12 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (9 5 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (5 5 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (5 5 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (5 5 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 4 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (4 4 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (4 4 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(CONSP-OF-BV-ARRAY-READ-SEGMENT
 (32 2 (:DEFINITION BV-ARRAY-READ-SEGMENT))
 (17 11 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (12 2 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (11 11 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (5 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE +-COMBINE-CONSTANTS))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (2 2 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (2 2 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(SUB1-PLUS1-INDUCT)
(CAR-OF-BV-ARRAY-READ-SEGMENT
 (103 6 (:REWRITE DEFAULT-CAR))
 (88 4 (:REWRITE CONSP-OF-BV-ARRAY-READ-SEGMENT))
 (71 38 (:REWRITE DEFAULT-<-1))
 (67 12 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (38 38 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-+-1))
 (27 27 (:REWRITE BOUND-WHEN-USB))
 (21 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (12 12 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (12 12 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (12 12 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (12 12 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (12 7 (:REWRITE +-COMBINE-CONSTANTS))
 (12 4 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (11 11 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (11 11 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 10 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (9 9 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (4 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:DEFINITION FIX))
 )
(TAKE-OF-BV-ARRAY-READ-SEGMENT
 (174 10 (:REWRITE DEFAULT-CDR))
 (157 27 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (154 76 (:REWRITE DEFAULT-<-1))
 (136 4 (:REWRITE CONSP-OF-BV-ARRAY-READ-SEGMENT))
 (129 129 (:REWRITE DEFAULT-+-2))
 (129 129 (:REWRITE DEFAULT-+-1))
 (77 76 (:REWRITE DEFAULT-<-2))
 (76 4 (:REWRITE CAR-OF-BV-ARRAY-READ-SEGMENT))
 (49 49 (:REWRITE BOUND-WHEN-USB))
 (39 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (32 32 (:REWRITE FOLD-CONSTS-IN-+))
 (28 8 (:REWRITE ZP-OPEN))
 (27 27 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (27 27 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (27 27 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (27 27 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (26 26 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (26 26 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (26 26 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (26 6 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (20 7 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (15 15 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (13 13 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (7 7 (:REWRITE <-OF-+-AND-+-COMBINE-CONSTANTS))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (5 5 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (3 3 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(CDR-OF-BV-ARRAY-READ-SEGMENT
 (25 13 (:REWRITE DEFAULT-<-1))
 (24 4 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (17 1 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9 9 (:REWRITE BOUND-WHEN-USB))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE +-COMBINE-CONSTANTS))
 (6 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 4 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (4 4 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (4 4 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (3 3 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (3 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (1 1 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 )
(NTHCDR-OF-BV-ARRAY-READ-SEGMENT
 (450 10 (:REWRITE NTHCDR-WHEN-<=-OF-LEN))
 (194 122 (:REWRITE DEFAULT-<-1))
 (175 163 (:REWRITE DEFAULT-+-2))
 (163 163 (:REWRITE DEFAULT-+-1))
 (144 24 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (136 122 (:REWRITE DEFAULT-<-2))
 (121 3 (:REWRITE LEN-OF-CDR))
 (95 95 (:REWRITE BOUND-WHEN-USB))
 (81 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (66 3 (:REWRITE DEFAULT-CDR))
 (59 11 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (59 3 (:REWRITE EQUAL-OF-LEN-AND-0))
 (43 15 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (41 41 (:REWRITE FOLD-CONSTS-IN-+))
 (41 22 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (40 8 (:DEFINITION POSP))
 (40 5 (:REWRITE <-OF-+-AND-+-COMBINE-CONSTANTS))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 24 (:REWRITE BV-ARRAY-READ-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (24 24 (:REWRITE BV-ARRAY-READ-WHEN-INDEX-IS-TOO-HIGH))
 (24 24 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 (24 24 (:REWRITE BV-ARRAY-READ-SHORTEN-DATA))
 (24 24 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (24 24 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (20 20 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 9 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (16 16 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (14 2 (:REWRITE CONSP-OF-BV-ARRAY-READ-SEGMENT))
 (13 13 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (13 13 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (8 8 (:TYPE-PRESCRIPTION POSP))
 (8 8 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (6 6 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 3 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (1 1 (:REWRITE EQUAL-OF-+-AND-+-CANCEL-CONSTANTS))
 )
(BV-ARRAY-TO-LIST-GEN)
(UNSIGNED-BYTE-LISTP-OF-BV-ARRAY-TO-LIST-GEN
 (12 1 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (1 1 (:REWRITE BV-ARRAYP-CONSTANT-OPENER))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 )
(BV-ARRAY-WRITE-SEGMENT
 (84 11 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (54 50 (:REWRITE DEFAULT-<-1))
 (53 50 (:REWRITE DEFAULT-<-2))
 (48 4 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (47 47 (:REWRITE BOUND-WHEN-USB))
 (47 42 (:REWRITE DEFAULT-+-2))
 (45 42 (:REWRITE DEFAULT-+-1))
 (35 35 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (29 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (22 10 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (21 21 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (20 20 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (20 2 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (13 1 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE USE-ALL-NATP-2))
 (12 12 (:REWRITE USE-ALL-NATP))
 (12 12 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (12 12 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (12 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (11 11 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (11 1 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (9 9 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (6 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (5 5 (:REWRITE BV-ARRAYP-CONSTANT-OPENER))
 (4 4 (:REWRITE BV-ARRAYP-WHEN-BV-ARRAYP-NARROWER))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 1 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
 (2 1 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
 (1 1 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (1 1 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 )
(BV-ARRAY-WRITE-SEGMENT-OUT-OF-ORDER
 (19 19 (:TYPE-PRESCRIPTION BV-ARRAY-WRITE-SEGMENT))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE BOUND-WHEN-USB))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 )
(BV-ARRAY-WRITE-SEGMENT-OF-CONS
 (50 5 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (40 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (28 6 (:REWRITE BV-ARRAY-WRITE-SEGMENT-OUT-OF-ORDER))
 (25 3 (:REWRITE DEFAULT-CDR))
 (25 3 (:REWRITE DEFAULT-CAR))
 (21 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (8 8 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (7 7 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (7 7 (:REWRITE BOUND-WHEN-USB))
 (7 7 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (7 7 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (6 2 (:REWRITE +-COMBINE-CONSTANTS))
 (5 5 (:TYPE-PRESCRIPTION NATP))
 (5 5 (:REWRITE USE-ALL-NATP-2))
 (5 5 (:REWRITE USE-ALL-NATP))
 (5 5 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (5 5 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:REWRITE BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES-GEN))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(BV-ARRAY-WRITE-SEGMENT-OF-APPEND
 (367 4 (:REWRITE CDR-OF-APPEND))
 (269 46 (:REWRITE DEFAULT-CDR))
 (266 28 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (208 161 (:REWRITE DEFAULT-+-2))
 (206 144 (:REWRITE DEFAULT-<-2))
 (175 43 (:REWRITE DEFAULT-CAR))
 (166 161 (:REWRITE DEFAULT-+-1))
 (157 144 (:REWRITE DEFAULT-<-1))
 (101 71 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (99 99 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (77 4 (:REWRITE CAR-OF-APPEND))
 (69 69 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (56 56 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (53 53 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (49 49 (:REWRITE BOUND-WHEN-USB))
 (48 37 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (42 2 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (41 41 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (34 29 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (33 10 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (32 28 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (29 29 (:REWRITE USE-ALL-NATP-2))
 (29 29 (:REWRITE USE-ALL-NATP))
 (29 29 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (29 29 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (28 28 (:TYPE-PRESCRIPTION NATP))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:REWRITE <-OF-+-AND-+-COMBINE-CONSTANTS))
 (18 18 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (16 16 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES-GEN))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (7 7 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 5 (:REWRITE EQUAL-OF-+-AND-+-CANCEL-CONSTANTS))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(LEN-OF-BV-ARRAY-WRITE-SEGMENT
 (170 18 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (128 8 (:REWRITE DEFAULT-CDR))
 (82 8 (:REWRITE DEFAULT-CAR))
 (81 31 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (62 55 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (55 55 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (44 36 (:REWRITE DEFAULT-<-2))
 (39 36 (:REWRITE DEFAULT-<-1))
 (32 2 (:REWRITE LEN-OF-CDR))
 (23 23 (:REWRITE BOUND-WHEN-USB))
 (18 18 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (16 8 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (12 10 (:REWRITE DEFAULT-+-2))
 (12 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (10 10 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (10 10 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (10 6 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (6 2 (:REWRITE +-COMBINE-CONSTANTS))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 2 (:REWRITE BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES-GEN))
 )
(BV-ARRAYP-OF-BV-ARRAY-WRITE-SEGMENT
 (144 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (116 7 (:REWRITE BV-ARRAYP-WHEN-NOT-CONSP))
 (62 12 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (54 54 (:TYPE-PRESCRIPTION LEN))
 (36 3 (:REWRITE DEFAULT-CAR))
 (32 24 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (30 30 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE BOUND-WHEN-USB))
 (24 24 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (24 2 (:REWRITE DEFAULT-CDR))
 (20 15 (:TYPE-PRESCRIPTION BV-ARRAY-WRITE-SEGMENT))
 (12 12 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 12 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (12 6 (:REWRITE LEN-OF-BV-ARRAY-WRITE-SEGMENT))
 (10 10 (:REWRITE BV-ARRAYP-CONSTANT-OPENER))
 (8 8 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:TYPE-PRESCRIPTION BV-ARRAY-WRITE))
 (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (4 4 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE BV-ARRAY-WRITE-WHEN-LEN-IS-NOT-NATP))
 (3 3 (:REWRITE BV-ARRAY-WRITE-WHEN-INDEX-NOT-INTEGER-CHEAP))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (2 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 )
(LIST-TO-BV-ARRAY-GEN
 (13 7 (:REWRITE DEFAULT-+-2))
 (12 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (10 10 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (8 7 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE DEFAULT-<-1))
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE BOUND-WHEN-USB))
 (4 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(LEN-OF-LIST-TO-BV-ARRAY-GEN
 (13 1 (:REWRITE BV-ARRAY-WRITE-SEGMENT-OUT-OF-ORDER))
 (8 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8 1 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (7 5 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (6 3 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION ARRAY-OF-ZEROS))
 (2 2 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE BOUND-WHEN-USB))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(BV-ARRAYP-OF-LIST-TO-BV-ARRAY-GEN
 (13 1 (:REWRITE BV-ARRAY-WRITE-SEGMENT-OUT-OF-ORDER))
 (12 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (8 1 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (6 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 )
