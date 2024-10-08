(INTEGERP-ALL-ONES
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (22 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (13 13 (:REWRITE DEFAULT-*-2))
 (13 13 (:REWRITE DEFAULT-*-1))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE MOD-WHEN-<-OF-0))
 (3 1 (:REWRITE MOD-WHEN-<))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-MOD-OF-+-WHEN-CONSTANTS))
 )
(LOGNOT-WHEN-NOT-INTEGERP)
(LOGNOT-OF-LOGNOT
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(<-OF-LOGNOT-ARG1-WHEN-CONSTANT
 (16 12 (:REWRITE DEFAULT-<-2))
 (14 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 )
(<-OF-LOGNOT-ARG2-WHEN-CONSTANT
 (16 12 (:REWRITE DEFAULT-<-1))
 (14 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 )
(LOGNOT-OF-ALL-ONES
 (93 93 (:TYPE-PRESCRIPTION EVENP))
 (62 31 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (62 31 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (62 31 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (49 5 (:REWRITE DEFAULT-+-2))
 (36 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (31 31 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (31 31 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (16 5 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LOGNOT-OF---OF-EXPT
 (81 81 (:TYPE-PRESCRIPTION EVENP))
 (54 27 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (54 27 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (54 27 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (27 27 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (27 27 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (25 3 (:REWRITE DEFAULT-+-2))
 (14 3 (:REWRITE DEFAULT-+-1))
 (12 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(EQUAL-OF-LOGNOT-AND-CONSTANT
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(LOGNOT-OF-FLOOR-OF-2
 (368 16 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG1))
 (161 73 (:REWRITE DEFAULT-+-2))
 (160 16 (:REWRITE INTEGERP-OF--))
 (160 16 (:REWRITE *-OF---ARG1))
 (156 108 (:REWRITE DEFAULT-*-2))
 (150 24 (:REWRITE FLOOR-WHEN-<))
 (140 108 (:REWRITE DEFAULT-*-1))
 (120 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (105 73 (:REWRITE DEFAULT-+-1))
 (91 67 (:REWRITE DEFAULT-<-1))
 (75 67 (:REWRITE DEFAULT-<-2))
 (64 8 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (64 8 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (49 3 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (42 26 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (42 26 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (42 26 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (42 14 (:REWRITE MOD-WHEN-<-OF-0))
 (37 21 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (32 16 (:DEFINITION FIX))
 (27 9 (:REWRITE MOD-WHEN-<))
 (26 26 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (25 25 (:REWRITE INTEGERP-OF-*))
 (17 17 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (17 17 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (17 17 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (16 16 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 (16 16 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
 (12 2 (:REWRITE FLOOR-OF-ONE-LESS-GEN))
 (9 9 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (9 9 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (9 9 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (9 9 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (9 9 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 (9 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (8 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (8 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (8 2 (:DEFINITION NATP))
 (6 2 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FLOOR-OF-LOGNOT-AND-2)
(LOGNOT-OF-*-OF-2
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(LOGNOT-OF-+-1-OF-*-2
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(INTEGERP-OF-*-1/2-OF-LOGNOT
 (6 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-OF-2))
 (2 2 (:REWRITE INTEGERP-OF-*))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(MOD-OF-LOGNOT-OF-2
 (1477 93 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (769 7 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (640 93 (:REWRITE MOD-WHEN-<-OF-0))
 (397 80 (:REWRITE COMMUTATIVITY-OF-*))
 (373 59 (:REWRITE MOD-WHEN-<))
 (254 142 (:REWRITE DEFAULT-<-1))
 (253 87 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (252 174 (:REWRITE DEFAULT-*-2))
 (240 174 (:REWRITE DEFAULT-*-1))
 (201 21 (:REWRITE *-OF---ARG1))
 (198 21 (:REWRITE INTEGERP-OF--))
 (170 92 (:REWRITE DEFAULT-+-2))
 (160 142 (:REWRITE DEFAULT-<-2))
 (159 7 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (154 92 (:REWRITE DEFAULT-+-1))
 (135 21 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (126 7 (:REWRITE INTEGERP-OF-+-OF-1/2-AND-*-OF-1/2))
 (107 59 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (107 59 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (107 59 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (107 59 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 (93 93 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (91 7 (:REWRITE DISTRIBUTIVITY))
 (87 87 (:REWRITE INTEGERP-OF-*))
 (83 57 (:REWRITE DEFAULT-UNARY-MINUS))
 (59 59 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (40 7 (:REWRITE *-OF---ARG2))
 (39 21 (:DEFINITION FIX))
 (21 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (7 7 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG2))
 (7 7 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 )
(<-OF-LOGNOT-AND-EXPT
 (618 618 (:TYPE-PRESCRIPTION EVENP))
 (412 206 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (412 206 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (412 206 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (206 206 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (206 206 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (63 19 (:REWRITE DEFAULT-<-2))
 (52 19 (:REWRITE DEFAULT-<-1))
 (32 10 (:REWRITE DEFAULT-+-2))
 (28 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (12 12 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (12 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (10 10 (:REWRITE DEFAULT-+-1))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (6 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(MOD-OF-LOGNOT-AND-EXPT
 (20610 5 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (20367 9 (:REWRITE INTEGERP-ALL-ONES))
 (13562 124 (:REWRITE MOD-WHEN-<))
 (11766 11766 (:TYPE-PRESCRIPTION EVENP))
 (7844 3922 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (7844 3922 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (7844 3922 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (4578 174 (:REWRITE MOD-WHEN-<-OF-0))
 (3922 3922 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (3922 3922 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (3319 131 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (3243 141 (:REWRITE DEFAULT-UNARY-/))
 (3074 14 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (2134 181 (:REWRITE DEFAULT-+-2))
 (1965 262 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (1965 262 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (1896 181 (:REWRITE DEFAULT-+-1))
 (1890 15 (:REWRITE <-OF---AND--))
 (1771 171 (:REWRITE DEFAULT-*-2))
 (1687 938 (:REWRITE DEFAULT-<-2))
 (1595 69 (:REWRITE INTEGERP-OF-*))
 (1544 124 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1488 124 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1430 30 (:REWRITE INTEGERP-OF--))
 (1354 938 (:REWRITE DEFAULT-<-1))
 (1249 131 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (1236 102 (:DEFINITION FIX))
 (1224 27 (:REWRITE COMMUTATIVITY-OF-*))
 (1090 9 (:REWRITE DISTRIBUTIVITY))
 (894 105 (:REWRITE DEFAULT-UNARY-MINUS))
 (782 262 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (741 57 (:REWRITE UNICITY-OF-1))
 (694 116 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (540 171 (:REWRITE DEFAULT-*-1))
 (477 10 (:REWRITE *-OF---ARG2))
 (475 475 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (475 475 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (443 44 (:REWRITE *-OF---ARG1))
 (415 131 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (262 262 (:LINEAR EXPT-BOUND-LINEAR))
 (262 262 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (262 262 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (235 131 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (189 63 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (180 124 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (180 124 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (174 174 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (131 131 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (131 131 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (131 131 (:LINEAR EXPT-BOUND-LINEAR-2))
 (93 15 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (18 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (5 5 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG2))
 (5 5 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 )
(MOD-OF-LOGNOT-OF-MOD-OF-EXPT-AND-EXPT
 (27934 208 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (13722 141 (:REWRITE MOD-WHEN-<))
 (13149 13149 (:TYPE-PRESCRIPTION EVENP))
 (11616 7 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (11183 5 (:REWRITE INTEGERP-ALL-ONES))
 (8766 4383 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (8766 4383 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (8766 4383 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (7606 209 (:REWRITE MOD-WHEN-<-OF-0))
 (4383 4383 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (4383 4383 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (4180 14 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (4094 178 (:REWRITE DEFAULT-UNARY-/))
 (3522 140 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (2898 23 (:REWRITE <-OF---AND--))
 (2441 199 (:REWRITE DEFAULT-+-1))
 (2386 46 (:REWRITE INTEGERP-OF--))
 (2221 199 (:REWRITE DEFAULT-+-2))
 (2151 236 (:REWRITE DEFAULT-*-2))
 (2100 280 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2100 280 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (1936 1046 (:REWRITE DEFAULT-<-2))
 (1931 89 (:REWRITE INTEGERP-OF-*))
 (1870 63 (:REWRITE COMMUTATIVITY-OF-*))
 (1752 141 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1692 141 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1638 135 (:DEFINITION FIX))
 (1553 140 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (1536 1046 (:REWRITE DEFAULT-<-1))
 (1259 154 (:REWRITE DEFAULT-UNARY-MINUS))
 (1136 9 (:REWRITE DISTRIBUTIVITY))
 (1053 236 (:REWRITE DEFAULT-*-1))
 (870 145 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (858 66 (:REWRITE UNICITY-OF-1))
 (850 59 (:REWRITE *-OF---ARG1))
 (840 280 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (609 14 (:REWRITE *-OF---ARG2))
 (526 526 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (526 526 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (420 140 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (400 40 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (280 280 (:LINEAR EXPT-BOUND-LINEAR))
 (280 280 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (280 280 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (240 80 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (214 140 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (209 209 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (201 141 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (201 141 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (141 23 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (140 140 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (140 140 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (140 140 (:LINEAR EXPT-BOUND-LINEAR-2))
 (30 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (26 26 (:REWRITE FOLD-CONSTS-IN-+))
 (9 9 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG2))
 (9 9 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 )
(FLOOR-OF-LOGNOT-AND-EXPT
 (7767 7767 (:TYPE-PRESCRIPTION EVENP))
 (6682 52 (:REWRITE FLOOR-WHEN-<))
 (5178 2589 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (5178 2589 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (5178 2589 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (4169 39 (:REWRITE MOD-WHEN-<))
 (2589 2589 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (2589 2589 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (1948 101 (:REWRITE DEFAULT-+-2))
 (1797 81 (:REWRITE DEFAULT-UNARY-/))
 (1444 615 (:REWRITE DEFAULT-<-2))
 (1230 52 (:REWRITE MOD-WHEN-<-OF-0))
 (1057 101 (:REWRITE DEFAULT-+-1))
 (1049 66 (:REWRITE DEFAULT-UNARY-MINUS))
 (986 98 (:REWRITE DEFAULT-*-2))
 (909 45 (:REWRITE INTEGERP-OF-*))
 (873 615 (:REWRITE DEFAULT-<-1))
 (732 6 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG1))
 (668 16 (:REWRITE INTEGERP-OF--))
 (579 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (558 6 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
 (542 60 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (520 180 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (504 4 (:REWRITE <-OF---AND--))
 (443 39 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (435 39 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (319 319 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (319 319 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (304 54 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (303 98 (:REWRITE DEFAULT-*-1))
 (277 7 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
 (250 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (233 17 (:REWRITE *-OF---ARG1))
 (202 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (180 180 (:LINEAR EXPT-BOUND-LINEAR))
 (180 180 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (180 180 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (90 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (90 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (90 90 (:LINEAR EXPT-BOUND-LINEAR-2))
 (88 52 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (75 25 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (57 33 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (52 52 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (52 52 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (47 39 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (47 39 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (31 5 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (16 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (14 14 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (14 9 (:REWRITE FLOOR-OF-ONE-LESS-GEN))
 (12 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (8 8 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (7 7 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 )
(<-OF---AND-LOGNOT
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(<-OF-LOGNOT-AND---OF-EXPT
 (405 405 (:TYPE-PRESCRIPTION EVENP))
 (270 135 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (270 135 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (270 135 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (135 135 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (135 135 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (60 16 (:REWRITE DEFAULT-<-2))
 (26 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE DEFAULT-<-1))
 (12 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (10 10 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 10 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (6 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(LOGNOT-OF-+-OF-EXPT
 (108 108 (:TYPE-PRESCRIPTION EVENP))
 (72 36 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (72 36 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (72 36 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (66 11 (:REWRITE DEFAULT-+-2))
 (55 11 (:REWRITE DEFAULT-+-1))
 (38 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 36 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (36 36 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SIGNED-BYTE-P-OF-LOGNOT
 (147 147 (:TYPE-PRESCRIPTION EVENP))
 (98 49 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (98 49 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (98 49 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (49 49 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (39 6 (:REWRITE DEFAULT-<-2))
 (36 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (17 6 (:REWRITE DEFAULT-<-1))
 (14 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 4 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 )
(EQUAL-OF-LOGNOT-AND-LOGNOT
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
