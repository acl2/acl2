(UNSIGNED-BYTE-P-FORCED-OF-BV-ARRAY-READ
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE BV-ARRAY-READ-WHEN-WIDTH-NEGATIVE))
 (1 1 (:REWRITE BV-ARRAY-READ-WHEN-EQUAL-OF-TAKE-AND-CONSTANT))
 )
(BV-ARRAY-READ-OF-*-ARG3
 (43 2 (:REWRITE BVCHOP-BOUND-2))
 (34 2 (:DEFINITION NTH))
 (24 1 (:DEFINITION EXPT))
 (23 15 (:REWRITE DEFAULT-<-2))
 (22 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (18 2 (:REWRITE ZP-OPEN))
 (17 15 (:REWRITE DEFAULT-<-1))
 (14 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 6 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (10 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (10 2 (:REWRITE UNSIGNED-BYTE-P-OF-NTH))
 (10 2 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (8 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 2 (:REWRITE <-OF-CEILING-OF-LG-ARG2-WHEN-CONSTANT))
 (7 1 (:REWRITE ZIP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 3 (:REWRITE DEFAULT-*-2))
 (5 5 (:TYPE-PRESCRIPTION POSP))
 (5 5 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (5 4 (:REWRITE DEFAULT-+-2))
 (5 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (3 1 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (3 1 (:DEFINITION POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (2 2 (:REWRITE BVCHOP-BOUND-OTHER))
 (2 2 (:REWRITE BVCHOP-BOUND))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BV-ARRAY-READ-OF-+-ARG3
 (43 2 (:REWRITE BVCHOP-BOUND-2))
 (34 2 (:DEFINITION NTH))
 (24 1 (:DEFINITION EXPT))
 (23 15 (:REWRITE DEFAULT-<-2))
 (22 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (18 2 (:REWRITE ZP-OPEN))
 (17 15 (:REWRITE DEFAULT-<-1))
 (14 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 6 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (10 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (10 2 (:REWRITE UNSIGNED-BYTE-P-OF-NTH))
 (10 2 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (8 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (8 2 (:REWRITE <-OF-CEILING-OF-LG-ARG2-WHEN-CONSTANT))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (7 1 (:REWRITE ZIP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (5 5 (:TYPE-PRESCRIPTION POSP))
 (5 5 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 1 (:REWRITE DEFAULT-*-2))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 1 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (3 1 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (3 1 (:DEFINITION POSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE BVCHOP-SUM-SUBST-CONST-ARG2))
 (2 2 (:REWRITE BVCHOP-SUM-SUBST-CONST))
 (2 2 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (2 2 (:REWRITE BVCHOP-CHOP-LEADING-CONSTANT))
 (2 2 (:REWRITE BVCHOP-BOUND-OTHER))
 (2 2 (:REWRITE BVCHOP-BOUND))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(BV-ARRAY-READ-TIGHTEN-FREE
 (51 2 (:REWRITE BVCHOP-BOUND-2))
 (34 2 (:DEFINITION NTH))
 (28 1 (:DEFINITION EXPT))
 (25 15 (:REWRITE DEFAULT-<-2))
 (22 22 (:TYPE-PRESCRIPTION CEILING-OF-LG))
 (22 15 (:REWRITE DEFAULT-<-1))
 (21 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (18 2 (:REWRITE ZP-OPEN))
 (15 2 (:REWRITE <-OF-CEILING-OF-LG-ARG2-WHEN-CONSTANT))
 (12 6 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (10 2 (:DEFINITION LEN))
 (9 6 (:REWRITE DEFAULT-+-2))
 (9 1 (:REWRITE ZIP-OPEN))
 (9 1 (:REWRITE UNSIGNED-BYTE-P-OF-CEILING-OF-LG-WHEN-<))
 (8 1 (:DEFINITION POSP))
 (7 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (6 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (5 1 (:REWRITE EQUAL-OF-0-AND-CEILING-OF-LG))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (4 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 1 (:REWRITE DEFAULT-*-2))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (2 2 (:REWRITE BVCHOP-BOUND-OTHER))
 (2 2 (:REWRITE BVCHOP-BOUND))
 (2 2 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 )
