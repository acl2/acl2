(BVMULT-OF-EXPT-GEN
 (1455 1455 (:TYPE-PRESCRIPTION EVENP))
 (971 486 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (971 486 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (971 486 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (942 11 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (486 486 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (486 486 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (307 20 (:REWRITE BVCHOP-IDENTITY))
 (270 37 (:REWRITE DEFAULT-*-2))
 (228 3 (:REWRITE BVCHOP-BOUND-2))
 (213 37 (:REWRITE DEFAULT-*-1))
 (150 121 (:REWRITE DEFAULT-<-1))
 (137 7 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (130 121 (:REWRITE DEFAULT-<-2))
 (121 121 (:REWRITE <-WHEN-BVLT))
 (117 117 (:TYPE-PRESCRIPTION IFIX))
 (97 14 (:REWRITE DEFAULT-+-2))
 (87 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (82 28 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (73 23 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (70 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (70 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (69 69 (:REWRITE BOUND-WHEN-USB))
 (61 13 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (45 1 (:REWRITE <-OF-*-AND-0))
 (43 43 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (43 43 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (41 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (41 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (40 28 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (39 39 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (28 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (28 2 (:REWRITE UNSIGNED-BYTE-P-OF-IF))
 (26 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (23 23 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (23 13 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (23 5 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (22 22 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (22 22 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (22 22 (:LINEAR <-OF-*-AND-*-LINEAR))
 (21 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-OF-EXPT))
 (20 20 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (20 20 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (18 1 (:REWRITE EQUAL-OF-0-AND-*))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (16 4 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (15 15 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 13 (:TYPE-PRESCRIPTION POSP))
 (13 13 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (12 12 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (8 2 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG2))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:DEFINITION FIX))
 (3 3 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (3 3 (:REWRITE BVCHOP-BOUND))
 (3 3 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (2 2 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (2 2 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(<-OF-BVMULT-ARG1-CORE-1
 (411 411 (:TYPE-PRESCRIPTION EVENP))
 (274 137 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (274 137 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (274 137 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (200 41 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (157 157 (:REWRITE DEFAULT-*-2))
 (157 157 (:REWRITE DEFAULT-*-1))
 (137 137 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (137 137 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (129 118 (:REWRITE DEFAULT-<-2))
 (118 118 (:REWRITE DEFAULT-<-1))
 (118 118 (:REWRITE <-WHEN-BVLT))
 (82 82 (:LINEAR <-OF-*-AND-*-LINEAR))
 (63 41 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (53 53 (:REWRITE BOUND-WHEN-USB))
 (53 41 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (36 30 (:LINEAR <=-OF-/-LINEAR))
 (32 8 (:REWRITE <-OF-/-AND-CONSTANT))
 (31 7 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (24 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (24 4 (:REWRITE <-OF-/-AND-CONSTANT-2))
 (24 4 (:REWRITE <-OF-/-AND-CONSTANT-1))
 (17 2 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (15 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (7 7 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (7 7 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (6 6 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (6 6 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (6 6 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (5 5 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (5 5 (:REWRITE MOD-WHEN-<-OF-0))
 (4 4 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (4 4 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 1 (:REWRITE MOD-WHEN-<))
 (4 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (4 1 (:REWRITE <-OF-0-AND-/))
 (3 3 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (3 3 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (1 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(<-OF-BVMULT-ARG1-CORE-2
 (1029 1029 (:TYPE-PRESCRIPTION EVENP))
 (686 343 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (686 343 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (686 343 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (343 343 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (343 343 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (218 108 (:REWRITE DEFAULT-*-2))
 (154 18 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (108 108 (:REWRITE DEFAULT-*-1))
 (82 71 (:REWRITE DEFAULT-<-2))
 (71 71 (:REWRITE DEFAULT-<-1))
 (71 71 (:REWRITE <-WHEN-BVLT))
 (36 36 (:LINEAR <-OF-*-AND-*-LINEAR))
 (33 33 (:REWRITE BOUND-WHEN-USB))
 (28 7 (:REWRITE MOD-WHEN-<))
 (28 7 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (25 25 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (24 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (23 23 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (21 21 (:REWRITE DEFAULT-UNARY-/))
 (18 18 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (18 18 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (18 18 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (18 12 (:LINEAR <=-OF-/-LINEAR))
 (15 3 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (14 7 (:REWRITE INTEGERP-OF-*))
 (12 3 (:REWRITE <-OF-/-AND-CONSTANT))
 (11 11 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (11 11 (:REWRITE MOD-WHEN-<-OF-0))
 (10 7 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (8 2 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (7 7 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (7 7 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (7 7 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (7 7 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (7 7 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (6 6 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (6 6 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (5 5 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (4 4 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
 (4 4 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (4 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (3 3 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (3 3 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(<-OF-BVMULT-ARG1-CORE
 (6878 19 (:REWRITE <-OF-0-AND-*))
 (4753 97 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (4428 494 (:REWRITE BVCHOP-IDENTITY))
 (4268 194 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (3395 97 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR))
 (2231 97 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (2100 2100 (:TYPE-PRESCRIPTION EVENP))
 (1985 397 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1497 797 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (1497 797 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (1497 797 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (1367 494 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (1168 101 (:REWRITE DEFAULT-+-2))
 (1162 34 (:REWRITE BVCHOP-BOUND-2))
 (1141 982 (:REWRITE DEFAULT-<-2))
 (1061 982 (:REWRITE DEFAULT-<-1))
 (985 719 (:REWRITE DEFAULT-*-2))
 (982 982 (:REWRITE <-WHEN-BVLT))
 (891 891 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (797 797 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (797 797 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (794 397 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (792 719 (:REWRITE DEFAULT-*-1))
 (627 292 (:LINEAR <-OF-*-AND-*-LINEAR))
 (588 588 (:REWRITE BOUND-WHEN-USB))
 (494 494 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (494 494 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (494 494 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (494 494 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (494 494 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (494 494 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (397 397 (:TYPE-PRESCRIPTION POSP))
 (397 397 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (397 397 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (397 397 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (308 28 (:REWRITE MOD-OF-1-ARG1))
 (228 228 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (228 228 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (194 194 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (194 97 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (130 26 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (123 42 (:REWRITE MOD-WHEN-<))
 (101 101 (:REWRITE DEFAULT-+-1))
 (97 97 (:REWRITE BVCHOP-OF-0-ARG1))
 (56 56 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (52 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (46 46 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (46 46 (:REWRITE MOD-WHEN-<-OF-0))
 (46 46 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (46 46 (:REWRITE EQUAL-WHEN-BVLT))
 (46 46 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (46 46 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (46 46 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (46 46 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (46 46 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (46 46 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (46 46 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (42 42 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (42 42 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (40 40 (:REWRITE DEFAULT-UNARY-/))
 (34 34 (:REWRITE BVCHOP-BOUND))
 (34 34 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (32 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (29 29 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (28 14 (:REWRITE UNICITY-OF-1))
 (26 26 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (26 26 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (26 13 (:REWRITE INTEGERP-OF-*))
 (20 4 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (20 4 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (20 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (20 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (18 18 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (16 16 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (16 16 (:LINEAR <=-OF-/-LINEAR))
 (16 4 (:REWRITE <-OF-/-AND-CONSTANT))
 (13 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (8 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (8 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (4 4 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (4 4 (:REWRITE BVMULT-SUBST2-ALT-CONSTANT-VERSION))
 (4 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (4 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (4 4 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (4 4 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (3 3 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 )
(<-OF-BVMULT-OF-CONSTANT-AND-CONSTANT
 (237 237 (:TYPE-PRESCRIPTION EVENP))
 (158 79 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (158 79 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (158 79 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (79 79 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (79 79 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (68 14 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (65 52 (:REWRITE DEFAULT-<-2))
 (59 55 (:REWRITE DEFAULT-*-2))
 (55 55 (:REWRITE DEFAULT-*-1))
 (54 52 (:REWRITE DEFAULT-<-1))
 (52 52 (:REWRITE <-WHEN-BVLT))
 (28 28 (:REWRITE BOUND-WHEN-USB))
 (28 28 (:LINEAR <-OF-*-AND-*-LINEAR))
 (28 4 (:REWRITE BVCHOP-IDENTITY))
 (20 4 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (20 4 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (20 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (16 16 (:LINEAR <=-OF-/-LINEAR))
 (16 4 (:REWRITE <-OF-/-AND-CONSTANT))
 (14 14 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (14 14 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (9 9 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 4 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (8 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 5 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (5 2 (:REWRITE MOD-WHEN-<))
 (5 1 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (5 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (5 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (4 4 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (4 4 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (4 1 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (4 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (3 3 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 2 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (1 1 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (1 1 (:REWRITE BVMULT-SUBST2-ALT-CONSTANT-VERSION))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 )
(BVLT-OF-CONSTANT-AND-BVMULT-OF-CONSTANT-ARG2
 (5601 5601 (:TYPE-PRESCRIPTION EVENP))
 (3734 1867 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (3734 1867 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (3734 1867 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (1867 1867 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (1867 1867 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (1298 356 (:REWRITE DEFAULT-*-2))
 (932 356 (:REWRITE DEFAULT-*-1))
 (252 252 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (252 252 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (252 252 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (252 252 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (252 252 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (252 252 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (218 185 (:REWRITE DEFAULT-<-2))
 (204 185 (:REWRITE DEFAULT-<-1))
 (185 185 (:REWRITE <-WHEN-BVLT))
 (85 1 (:DEFINITION IFF))
 (59 4 (:REWRITE <-OF-0-AND-*))
 (50 50 (:REWRITE BOUND-WHEN-USB))
 (38 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (35 35 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (30 6 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (26 26 (:LINEAR <=-OF-/-LINEAR))
 (24 6 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (24 6 (:REWRITE <-OF-/-AND-CONSTANT))
 (24 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (21 3 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (17 6 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (17 6 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (15 15 (:REWRITE DEFAULT-UNARY-/))
 (15 4 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (13 13 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (13 13 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (13 13 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (13 13 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (12 12 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (12 12 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (12 3 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (11 11 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (9 9 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (8 8 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (8 8 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (8 8 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (8 2 (:REWRITE MOD-WHEN-<))
 (8 2 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (8 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (7 7 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (6 6 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (6 2 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (5 5 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (4 3 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE INTEGERP-OF-*))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (3 3 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (3 3 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE NOT-BVLT-OF-MAX-ARG2-CONSTANT-VERSION))
 (3 3 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (3 3 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (3 3 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-MORE))
 (3 3 (:REWRITE BVLT-WHEN-NOT-BVLT-ONE-LESS))
 (3 3 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (3 3 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (3 3 (:REWRITE BVLT-WHEN-BVLT-SMALLER))
 (3 3 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (3 3 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (3 3 (:REWRITE BVLT-WHEN-BVLT-FALSE2))
 (3 3 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (3 3 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (3 3 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (3 3 (:REWRITE BVLT-UNIQUE))
 (3 3 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (3 3 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (3 3 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (3 3 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (3 3 (:REWRITE BVLT-TRANSITIVE-5-B))
 (3 3 (:REWRITE BVLT-TRANSITIVE-5-A))
 (3 3 (:REWRITE BVLT-TRANSITIVE-4-B))
 (3 3 (:REWRITE BVLT-TRANSITIVE-4-A))
 (3 3 (:REWRITE BVLT-TRANSITIVE-3-B))
 (3 3 (:REWRITE BVLT-TRANSITIVE-3-A))
 (3 3 (:REWRITE BVLT-TRANSITIVE-2-B))
 (3 3 (:REWRITE BVLT-TRANSITIVE-2-A))
 (3 3 (:REWRITE BVLT-TRANSITIVE-1-B))
 (3 3 (:REWRITE BVLT-TRANSITIVE-1-A))
 (3 3 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (3 3 (:REWRITE BVLT-OF-MAX-ARG3-CONSTANT-VERSION))
 (3 3 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (3 3 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (2 2 (:REWRITE BVMULT-SUBST2-ALT-CONSTANT-VERSION))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:TYPE-PRESCRIPTION BVMULT))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (1 1 (:REWRITE <-OF-BVMULT-OF-CONSTANT-AND-CONSTANT))
 )
(<-OF-BVMULT-ARG2-CORE
 (591 591 (:TYPE-PRESCRIPTION EVENP))
 (394 197 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (394 197 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (394 197 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (197 197 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (197 197 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (57 9 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (53 31 (:REWRITE DEFAULT-<-2))
 (48 9 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (35 35 (:REWRITE DEFAULT-*-2))
 (35 35 (:REWRITE DEFAULT-*-1))
 (31 31 (:REWRITE DEFAULT-<-1))
 (31 31 (:REWRITE <-WHEN-BVLT))
 (20 20 (:REWRITE BOUND-WHEN-USB))
 (18 18 (:LINEAR <-OF-*-AND-*-LINEAR))
 (18 12 (:LINEAR <=-OF-/-LINEAR))
 (15 3 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (12 3 (:REWRITE <-OF-/-AND-CONSTANT))
 (10 10 (:REWRITE DEFAULT-UNARY-/))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (8 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (5 5 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (5 5 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (5 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (5 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (3 3 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (3 3 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 )
(<-OF-CONSTANT-AND-BVMULT-OF-CONSTANT
 (591 591 (:TYPE-PRESCRIPTION EVENP))
 (394 197 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (394 197 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (394 197 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (197 197 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (197 197 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (57 9 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (53 31 (:REWRITE DEFAULT-<-2))
 (48 9 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (35 35 (:REWRITE DEFAULT-*-2))
 (35 35 (:REWRITE DEFAULT-*-1))
 (31 31 (:REWRITE DEFAULT-<-1))
 (31 31 (:REWRITE <-WHEN-BVLT))
 (20 20 (:REWRITE BOUND-WHEN-USB))
 (18 18 (:LINEAR <-OF-*-AND-*-LINEAR))
 (18 12 (:LINEAR <=-OF-/-LINEAR))
 (15 3 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (12 3 (:REWRITE <-OF-/-AND-CONSTANT))
 (10 10 (:REWRITE DEFAULT-UNARY-/))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (9 9 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (8 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (5 5 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (5 5 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (5 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (5 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (3 3 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (3 3 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-*-GEN))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 )
(BVLT-OF-CONSTANT-AND-BVMULT-OF-CONSTANT
 (5073 5073 (:TYPE-PRESCRIPTION EVENP))
 (3382 1691 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (3382 1691 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (3382 1691 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (1691 1691 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (1691 1691 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (1212 347 (:REWRITE DEFAULT-*-2))
 (879 347 (:REWRITE DEFAULT-*-1))
 (780 5 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (380 20 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (244 244 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (244 244 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (244 244 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (244 244 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (244 244 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (244 244 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (243 199 (:REWRITE DEFAULT-<-2))
 (226 199 (:REWRITE DEFAULT-<-1))
 (199 199 (:REWRITE <-WHEN-BVLT))
 (190 5 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (180 5 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (165 5 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (80 20 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (80 20 (:REWRITE MOD-WHEN-<))
 (80 20 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (75 75 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (75 75 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (75 75 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (59 4 (:REWRITE <-OF-0-AND-*))
 (44 44 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (40 20 (:REWRITE INTEGERP-OF-*))
 (38 38 (:REWRITE BOUND-WHEN-USB))
 (33 33 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (25 25 (:REWRITE DEFAULT-UNARY-/))
 (24 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (20 20 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (20 20 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (20 20 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (20 20 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (20 20 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (20 20 (:REWRITE MOD-WHEN-<-OF-0))
 (20 20 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (20 5 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (15 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (13 13 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (13 13 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (12 12 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (12 12 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (11 11 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (10 10 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 10 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (10 10 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (10 2 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (8 2 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (8 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (6 2 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (5 5 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (3 2 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (2 2 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NOT-BVLT-OF-MAX-ARG2-CONSTANT-VERSION))
 (2 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (2 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (2 2 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (2 2 (:REWRITE BVMULT-SUBST2-ALT-CONSTANT-VERSION))
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
 (2 2 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:TYPE-PRESCRIPTION BVMULT))
 )
