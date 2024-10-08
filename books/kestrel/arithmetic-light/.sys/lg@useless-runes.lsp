(LG)
(LG-OF-EXPT
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 )
(EQUAL-OF-0-AND-LG
 (22 1 (:DEFINITION INTEGER-LENGTH))
 (10 2 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 1 (:REWRITE FLOOR-WHEN-<))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION FLOOR))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (1 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (1 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 )
(NATP-OF-LG
 (5 1 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(POSP-OF-LG
 (350 5 (:REWRITE <-OF-INTEGER-LENGTH-ARG2))
 (174 4 (:REWRITE <-OF-1-AND-INTEGER-LENGTH))
 (96 3 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (91 91 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (91 91 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (91 91 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (91 91 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (91 91 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (91 91 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (90 3 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (75 3 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (61 41 (:REWRITE DEFAULT-<-2))
 (53 19 (:REWRITE FLOOR-WHEN-<))
 (51 3 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (45 3 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (41 41 (:REWRITE DEFAULT-<-1))
 (31 7 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (19 19 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (19 19 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (19 19 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (19 19 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (18 6 (:REWRITE COMMUTATIVITY-OF-*))
 (17 17 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (13 8 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ZIP-OPEN))
 (3 3 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 )
(NATP-OF-LG-TYPE
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(EXPT-OF-LG-WHEN-POWER-OF-2P
 (12 12 (:TYPE-PRESCRIPTION EVENP))
 (8 4 (:TYPE-PRESCRIPTION NATP-OF-LG-TYPE))
 (8 4 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (8 4 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (8 4 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 )
(<=-OF-EXPT-2-OF-LG-LINEAR
 (90 90 (:TYPE-PRESCRIPTION EVENP))
 (60 30 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (60 30 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (60 30 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (50 1 (:LINEAR EXPT-HALF-LINEAR))
 (45 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (30 30 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (30 5 (:REWRITE <-OF-INTEGER-LENGTH-ARG2))
 (26 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (24 4 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (20 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (16 8 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (13 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (13 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (13 1 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (12 4 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (10 5 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (10 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (10 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (8 8 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (5 5 (:TYPE-PRESCRIPTION POWER-OF-2P))
 (5 1 (:REWRITE +-OF-EXPT2-OF-ONE-LESS-AND-EXPT2-OF-ONE-LESS))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (2 2 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(<=-OF-EXPT-2-OF-+-OF-1-AND-LG-LINEAR
 (135 135 (:TYPE-PRESCRIPTION EVENP))
 (90 45 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (90 45 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (90 45 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (45 45 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (28 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (28 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (24 8 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (22 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (15 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (15 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (12 4 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (11 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (11 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (2 2 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-EXPT-2))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(<-OF-EXPT-2-OF-LG-SAME
 (63 63 (:TYPE-PRESCRIPTION EVENP))
 (42 21 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (42 21 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (42 21 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (2 1 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 1 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE <-OF-EXPT-2-AND-CONSTANT))
 )
(<-OF-EXPT-2-OF-LG-SAME-LINEAR
 (936 936 (:TYPE-PRESCRIPTION EVENP))
 (631 319 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (380 24 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (275 5 (:REWRITE <-OF-EXPT-2-AND-CONSTANT))
 (260 25 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (194 12 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (194 12 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (165 145 (:REWRITE DEFAULT-<-2))
 (150 145 (:REWRITE DEFAULT-<-1))
 (136 68 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (136 24 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (133 33 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (102 12 (:REWRITE EQUAL-OF-EXPT2-AND-CONSTANT))
 (100 15 (:DEFINITION NATP))
 (80 5 (:REWRITE EQUAL-OF-1-AND-EXPT))
 (68 68 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (68 12 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (68 12 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (60 5 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (59 31 (:REWRITE DEFAULT-+-2))
 (48 36 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (31 31 (:TYPE-PRESCRIPTION POSP))
 (31 31 (:REWRITE DEFAULT-+-1))
 (30 10 (:REWRITE EQUAL-OF-1-AND-INTEGER-LENGTH))
 (25 5 (:REWRITE <-OF-0-AND-INTEGER-LENGTH))
 (24 24 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (24 24 (:LINEAR EXPT-BOUND-LINEAR))
 (24 24 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (24 24 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (22 9 (:REWRITE DEFAULT-*-2))
 (20 10 (:DEFINITION IFIX))
 (20 5 (:REWRITE <-OF-1-AND-INTEGER-LENGTH))
 (17 17 (:LINEAR EXPT-BOUND-LINEAR-2))
 (15 15 (:TYPE-PRESCRIPTION NATP))
 (10 2 (:REWRITE +-OF-EXPT2-OF-ONE-LESS-AND-EXPT2-OF-ONE-LESS))
 (9 9 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 )
(<-OF-LG-AND-0
 (6 3 (:TYPE-PRESCRIPTION NATP-OF-LG-TYPE))
 (5 1 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (3 1 (:DEFINITION POSP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LG-OF-*-OF-1/2
 (10 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (2 2 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 )
(<-OF-LG-WHEN-UNSIGNED-BYTE-P
 (123 123 (:TYPE-PRESCRIPTION EVENP))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (48 1 (:LINEAR EXPT-HALF-LINEAR))
 (45 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (41 41 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (30 5 (:REWRITE <-OF-INTEGER-LENGTH-ARG2))
 (28 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (22 19 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (19 19 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (18 9 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (14 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (14 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (14 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (12 1 (:REWRITE DEFAULT-*-2))
 (9 9 (:TYPE-PRESCRIPTION POWER-OF-2P))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (5 1 (:REWRITE +-OF-EXPT2-OF-ONE-LESS-AND-EXPT2-OF-ONE-LESS))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (3 3 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(<-OF-LG-WHEN-UNSIGNED-BYTE-P-CHEAP
 (123 123 (:TYPE-PRESCRIPTION EVENP))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (48 1 (:LINEAR EXPT-HALF-LINEAR))
 (45 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (41 41 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (30 5 (:REWRITE <-OF-INTEGER-LENGTH-ARG2))
 (28 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (22 19 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (19 19 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (18 9 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (14 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (14 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (14 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (12 1 (:REWRITE DEFAULT-*-2))
 (9 9 (:TYPE-PRESCRIPTION POWER-OF-2P))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (5 1 (:REWRITE +-OF-EXPT2-OF-ONE-LESS-AND-EXPT2-OF-ONE-LESS))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (3 3 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
