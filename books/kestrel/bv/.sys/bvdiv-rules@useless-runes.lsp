(EQUAL-OF-0-AND-BVDIV
 (563 7 (:REWRITE BVCHOP-BOUND-2))
 (484 1 (:REWRITE FLOOR-WHEN-<))
 (240 16 (:DEFINITION EXPT))
 (229 5 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (213 10 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (198 5 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR))
 (92 20 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (90 53 (:REWRITE DEFAULT-<-1))
 (67 27 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (61 61 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (61 61 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (58 53 (:REWRITE DEFAULT-<-2))
 (57 57 (:REWRITE <-WHEN-BVLT))
 (50 50 (:REWRITE BOUND-WHEN-USB))
 (48 16 (:REWRITE DEFAULT-*-2))
 (48 16 (:REWRITE COMMUTATIVITY-OF-+))
 (47 37 (:REWRITE DEFAULT-+-2))
 (45 5 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (40 20 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (40 20 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (37 37 (:REWRITE DEFAULT-+-1))
 (27 27 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (27 27 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (27 27 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (26 26 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (25 25 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (25 25 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (24 24 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (21 21 (:TYPE-PRESCRIPTION POSP))
 (20 20 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (20 20 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (16 16 (:REWRITE ZIP-OPEN))
 (16 16 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (12 12 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 1 (:REWRITE BVDIV-WHEN-<))
 (9 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (8 8 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (7 7 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (7 1 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (5 5 (:REWRITE BVCHOP-OF-0-ARG1))
 (5 1 (:REWRITE BVDIV-WHEN-SIZE-IS-NOT-POSITIVE))
 (5 1 (:DEFINITION POSP))
 (4 4 (:REWRITE BVCHOP-BOUND-OTHER))
 (4 4 (:REWRITE BVCHOP-BOUND))
 (3 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (2 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (2 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (2 1 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE BVDIV-WHEN-NOT-INTEGERP-ARG2))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG2))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (1 1 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (1 1 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NOT-BVLT-OF-MAX-ARG2-CONSTANT-VERSION))
 (1 1 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (1 1 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE-ALT))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (1 1 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-MORE))
 (1 1 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-LESS))
 (1 1 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-SMALLER))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-FALSE2))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (1 1 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (1 1 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (1 1 (:REWRITE BVLT-UNIQUE))
 (1 1 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (1 1 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (1 1 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (1 1 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (1 1 (:REWRITE BVLT-TRANSITIVE-5-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-5-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-4-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-4-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-3-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-3-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-2-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-2-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-1-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-1-A))
 (1 1 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (1 1 (:REWRITE BVLT-OF-MAX-ARG3-CONSTANT-VERSION))
 (1 1 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (1 1 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (1 1 (:REWRITE BVDIV-OF-CONSTANT-TRIM-ARG1))
 )
(BVLT-OF-0-AND-BVDIV
 (485 2 (:REWRITE FLOOR-WHEN-<))
 (473 8 (:REWRITE BVCHOP-BOUND-2))
 (330 22 (:DEFINITION EXPT))
 (158 3 (:DEFINITION POSP))
 (139 31 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (123 75 (:REWRITE DEFAULT-<-1))
 (101 45 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (90 75 (:REWRITE DEFAULT-<-2))
 (79 79 (:REWRITE <-WHEN-BVLT))
 (69 69 (:REWRITE BOUND-WHEN-USB))
 (66 22 (:REWRITE DEFAULT-*-2))
 (66 22 (:REWRITE COMMUTATIVITY-OF-+))
 (65 51 (:REWRITE DEFAULT-+-2))
 (63 7 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (62 31 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (62 31 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (51 51 (:REWRITE DEFAULT-+-1))
 (45 45 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (45 45 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (45 45 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (41 41 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (38 38 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (38 38 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (36 36 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (34 34 (:TYPE-PRESCRIPTION POSP))
 (31 31 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (31 31 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (22 22 (:REWRITE ZIP-OPEN))
 (22 22 (:REWRITE DEFAULT-*-1))
 (18 18 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (18 2 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 16 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (16 16 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (14 2 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (13 2 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (10 1 (:REWRITE BVDIV-WHEN-<))
 (9 9 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (8 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (8 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (7 7 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (7 7 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (5 1 (:REWRITE BVDIV-WHEN-SIZE-IS-NOT-POSITIVE))
 (4 4 (:REWRITE BVCHOP-BOUND))
 (4 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (3 3 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (3 3 (:REWRITE EQUAL-WHEN-BVLT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE BVCHOP-BOUND-OTHER))
 (3 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (3 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (3 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (3 2 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (2 2 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (2 2 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NOT-BVLT-OF-MAX-ARG2-CONSTANT-VERSION))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE-ALT))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-MORE))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-LESS))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-SMALLER))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-FALSE2))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (2 2 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (2 2 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (2 2 (:REWRITE BVLT-UNIQUE))
 (2 2 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (2 2 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (2 2 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (2 2 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (2 2 (:REWRITE BVLT-TRANSITIVE-5-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-5-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-4-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-4-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-3-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-3-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-2-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-2-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-1-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-1-A))
 (2 2 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-OF-MAX-ARG3-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (2 2 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (2 1 (:REWRITE BVDIV-WHEN-NOT-INTEGERP-ARG2))
 (1 1 (:REWRITE BVDIV-OF-CONSTANT-TRIM-ARG1))
 )
(BVLT-OF-BVDIV-CONSTANTS
 (672 3 (:REWRITE FLOOR-WHEN-<))
 (450 30 (:DEFINITION EXPT))
 (210 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (204 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (195 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR))
 (172 110 (:REWRITE DEFAULT-<-1))
 (112 112 (:REWRITE <-WHEN-BVLT))
 (110 110 (:REWRITE DEFAULT-<-2))
 (99 99 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (99 99 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (99 99 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (99 99 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (99 99 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (97 37 (:REWRITE DEFAULT-*-2))
 (91 91 (:REWRITE BOUND-WHEN-USB))
 (90 30 (:REWRITE COMMUTATIVITY-OF-+))
 (73 17 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (63 63 (:REWRITE DEFAULT-+-2))
 (63 63 (:REWRITE DEFAULT-+-1))
 (47 23 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (37 37 (:REWRITE DEFAULT-*-1))
 (36 36 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (34 17 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (31 17 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (30 30 (:REWRITE ZIP-OPEN))
 (27 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (25 25 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (25 25 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (23 23 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (23 23 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (20 20 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (20 20 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (19 19 (:TYPE-PRESCRIPTION POSP))
 (17 17 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (17 17 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (14 2 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (12 2 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (10 2 (:DEFINITION POSP))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (7 7 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (7 7 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (7 1 (:REWRITE BVDIV-WHEN-<))
 (6 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (6 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (6 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (6 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (5 5 (:REWRITE BVCHOP-BOUND))
 (5 1 (:REWRITE BVDIV-WHEN-SIZE-IS-NOT-POSITIVE))
 (4 4 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (4 4 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE BVCHOP-OF-0-ARG1))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (2 2 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NOT-BVLT-OF-MAX-ARG2-CONSTANT-VERSION))
 (2 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (2 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-MORE))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-LESS))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-SMALLER))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-FALSE2))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (2 2 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (2 2 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (2 2 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVLT-UNIQUE))
 (2 2 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (2 2 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (2 2 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (2 2 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (2 2 (:REWRITE BVLT-TRANSITIVE-5-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-5-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-4-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-4-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-3-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-3-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-2-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-2-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-1-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-1-A))
 (2 2 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-OF-MAX-ARG3-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (2 2 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (2 1 (:REWRITE BVDIV-WHEN-NOT-INTEGERP-ARG2))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE BVDIV-OF-CONSTANT-TRIM-ARG1))
 )
(<-OF-BVDIV-SAME
 (4664 30 (:REWRITE FLOOR-WHEN-<))
 (3180 137 (:DEFINITION EXPT))
 (2793 52 (:REWRITE BVCHOP-BOUND-2))
 (1579 154 (:REWRITE BVCHOP-IDENTITY))
 (928 166 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (915 519 (:REWRITE DEFAULT-<-2))
 (839 130 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (802 519 (:REWRITE DEFAULT-<-1))
 (799 269 (:REWRITE DEFAULT-*-2))
 (786 262 (:REWRITE COMMUTATIVITY-OF-+))
 (665 19 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (584 6 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (541 541 (:REWRITE <-WHEN-BVLT))
 (539 531 (:REWRITE DEFAULT-+-2))
 (538 476 (:REWRITE BOUND-WHEN-USB))
 (531 531 (:REWRITE DEFAULT-+-1))
 (359 130 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (355 7 (:REWRITE FLOOR-BOUND-STRICT))
 (338 338 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (271 269 (:REWRITE DEFAULT-*-1))
 (260 130 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (259 130 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (254 132 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (232 130 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (216 6 (:REWRITE DEFAULT-UNARY-/))
 (214 214 (:TYPE-PRESCRIPTION NATP))
 (200 166 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (190 13 (:REWRITE UNSIGNED-BYTE-P-OF-FLOOR))
 (185 185 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (185 185 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (185 185 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (184 184 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (180 6 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (178 178 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (178 178 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (178 178 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (174 166 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (166 166 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (156 156 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (137 137 (:REWRITE ZIP-OPEN))
 (130 130 (:TYPE-PRESCRIPTION POSP))
 (114 14 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG2))
 (111 111 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (111 111 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (110 11 (:REWRITE UNSIGNED-BYTE-P-BVCHOP-SAME))
 (96 7 (:REWRITE <=-OF-FLOOR-SAME-WHEN-NEGATIVE-INTEGER-2))
 (96 7 (:REWRITE <=-OF-FLOOR-SAME-WHEN-NEGATIVE-INTEGER))
 (79 14 (:REWRITE UNSIGNED-BYTE-P-OF-1))
 (65 14 (:DEFINITION POSP))
 (64 30 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (53 53 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (52 52 (:REWRITE BVCHOP-BOUND))
 (36 30 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (36 30 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (36 30 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (30 30 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (30 3 (:REWRITE BVDIV-WHEN-<))
 (25 25 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (25 25 (:REWRITE EQUAL-WHEN-BVLT))
 (25 25 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (25 25 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (25 25 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (25 25 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (25 25 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (25 25 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (25 25 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (24 24 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (24 3 (:REWRITE BVDIV-WHEN-SIZE-IS-NOT-POSITIVE))
 (21 21 (:REWRITE BVCHOP-UPPER-BOUND))
 (19 19 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (19 19 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE-ALT))
 (19 19 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE))
 (19 19 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (19 19 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (19 19 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (19 19 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (15 15 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (13 13 (:REWRITE BVCHOP-BOUND-OTHER))
 (9 9 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (6 3 (:REWRITE BVDIV-WHEN-NOT-INTEGERP-ARG2))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (3 3 (:REWRITE BVDIV-OF-CONSTANT-TRIM-ARG1))
 (2 1 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 )
