(EXPT2$INLINE
 (99 99 (:TYPE-PRESCRIPTION EVENP))
 (66 33 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (66 33 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (66 33 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (33 33 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (24 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (24 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (24 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (24 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (24 2 (:REWRITE FLOOR-WHEN-<))
 (14 14 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (14 14 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (14 14 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (14 14 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (14 14 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (14 14 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (3 3 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (3 3 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 )
(IMOD$INLINE
 (45 45 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (45 45 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (17 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE MOD-WHEN-<-OF-0))
 (4 2 (:REWRITE MOD-WHEN-<))
 (4 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (4 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (3 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (2 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(LOGHEAD$INLINE
 (370 3 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (282 282 (:TYPE-PRESCRIPTION EVENP))
 (188 94 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (188 94 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (188 94 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (103 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (94 94 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (94 94 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (93 3 (:REWRITE MOD-WHEN-<))
 (92 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (91 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (72 6 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (72 6 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (72 6 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (72 6 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (72 6 (:REWRITE FLOOR-WHEN-<))
 (61 25 (:REWRITE DEFAULT-<-1))
 (60 8 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (58 25 (:REWRITE DEFAULT-<-2))
 (48 48 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (48 4 (:REWRITE DEFAULT-+-2))
 (36 3 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (36 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (24 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (23 1 (:REWRITE DEFAULT-UNARY-/))
 (20 20 (:TYPE-PRESCRIPTION LOGAND-NON-NEGATIVE-TYPE))
 (20 20 (:TYPE-PRESCRIPTION LOGAND-NEGATIVE-TYPE))
 (13 13 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (13 13 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (13 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (12 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (12 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (12 1 (:REWRITE DEFAULT-*-2))
 (8 8 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (8 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (8 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (6 6 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (5 3 (:REWRITE MOD-WHEN-<-OF-0))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (4 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (3 3 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (3 3 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(LOGAPP
 (370 3 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (303 303 (:TYPE-PRESCRIPTION EVENP))
 (217 116 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (217 116 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (217 116 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (103 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (93 3 (:REWRITE MOD-WHEN-<))
 (92 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (91 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (61 28 (:REWRITE DEFAULT-<-2))
 (60 8 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (59 2 (:REWRITE FLOOR-WHEN-<))
 (54 4 (:REWRITE DEFAULT-+-2))
 (54 4 (:REWRITE DEFAULT-+-1))
 (50 28 (:REWRITE DEFAULT-<-1))
 (48 4 (:REWRITE DEFAULT-*-2))
 (39 39 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (36 3 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (36 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (24 24 (:TYPE-PRESCRIPTION <=-OF-FLOOR-WHEN-<-TYPE))
 (24 24 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (24 24 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (24 24 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (24 24 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (24 24 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (24 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (24 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (24 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (24 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (24 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (23 1 (:REWRITE DEFAULT-UNARY-/))
 (13 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (12 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (12 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (10 10 (:REWRITE EXPT-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 10 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (8 8 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (8 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (8 8 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (5 3 (:REWRITE MOD-WHEN-<-OF-0))
 (4 4 (:REWRITE DEFAULT-*-1))
 (4 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (4 4 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (3 3 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (3 3 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 )
