(PFIELD::INV
 (64 5 (:REWRITE MOD-WHEN-MULTIPLE))
 (64 5 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (38 10 (:REWRITE COMMUTATIVITY-OF-*))
 (33 5 (:REWRITE MOD-WHEN-<-OF-0))
 (28 20 (:REWRITE DEFAULT-*-2))
 (28 20 (:REWRITE DEFAULT-*-1))
 (21 21 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (21 21 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (21 11 (:REWRITE DEFAULT-<-1))
 (18 10 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (18 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (13 13 (:TYPE-PRESCRIPTION PFIELD::<-OF-0--AND-MINUS1-TYPE))
 (11 11 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-UNARY-/))
 (8 4 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (8 4 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (8 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (5 5 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (4 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 )
(PFIELD::NATP-OF-INV)
(PFIELD::FEP-OF-INV
 (65 7 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (49 5 (:REWRITE MOD-WHEN-MULTIPLE))
 (36 12 (:REWRITE COMMUTATIVITY-OF-*))
 (30 12 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (24 24 (:REWRITE DEFAULT-*-2))
 (24 24 (:REWRITE DEFAULT-*-1))
 (21 7 (:REWRITE MOD-WHEN-<-OF-0))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (15 5 (:REWRITE MOD-WHEN-<))
 (12 12 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (12 12 (:REWRITE DEFAULT-UNARY-/))
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (7 7 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (6 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (5 5 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (5 5 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (5 5 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (5 5 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 1 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 )
(PFIELD::<-OF-INV
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 )
(PFIELD::INV-OF-0
 (12 1 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (5 1 (:REWRITE PFIELD::FEP-OF-0))
 (4 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (3 2 (:REWRITE DEFAULT-<-2))
 (3 1 (:DEFINITION POSP))
 (2 2 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE MOD-WHEN-<-OF-0))
 )
(PFIELD::MUL-OF-INV-ARG2
 (66 8 (:REWRITE MOD-WHEN-MULTIPLE))
 (37 37 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (32 32 (:REWRITE DEFAULT-*-2))
 (32 32 (:REWRITE DEFAULT-*-1))
 (32 14 (:REWRITE MOD-WHEN-<-OF-0))
 (22 8 (:REWRITE MOD-WHEN-<))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE DEFAULT-UNARY-/))
 (16 4 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (14 14 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (8 8 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (8 8 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (8 8 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (8 8 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (8 8 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (5 5 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (4 4 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (4 4 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 4 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (4 4 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 )
(PFIELD::INV-OF-MUL
 (410 50 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (346 42 (:REWRITE MOD-WHEN-MULTIPLE))
 (276 92 (:REWRITE COMMUTATIVITY-OF-*))
 (184 184 (:REWRITE DEFAULT-*-2))
 (184 184 (:REWRITE DEFAULT-*-1))
 (152 92 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (150 50 (:REWRITE MOD-WHEN-<-OF-0))
 (126 42 (:REWRITE MOD-WHEN-<))
 (119 119 (:REWRITE DEFAULT-<-2))
 (119 119 (:REWRITE DEFAULT-<-1))
 (64 64 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (60 20 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (52 52 (:REWRITE DEFAULT-UNARY-/))
 (50 50 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (42 42 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (33 9 (:REWRITE PFIELD::POW-OF-+))
 (23 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (20 20 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 (14 10 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (14 10 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 (8 8 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 )
(PFIELD::INV-OF-+-SAME-ARG1
 (60 60 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (60 60 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (60 14 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (53 53 (:REWRITE DEFAULT-<-2))
 (53 53 (:REWRITE DEFAULT-<-1))
 (48 6 (:REWRITE MOD-WHEN-MULTIPLE))
 (42 14 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (42 14 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (24 8 (:REWRITE MOD-WHEN-<-OF-0))
 (20 20 (:REWRITE DEFAULT-*-2))
 (20 20 (:REWRITE DEFAULT-*-1))
 (13 13 (:REWRITE DEFAULT-UNARY-/))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (9 9 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (9 3 (:REWRITE MOD-WHEN-<))
 (8 8 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (8 8 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (8 2 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (6 6 (:REWRITE INVERSE-OF-*))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 )
(PFIELD::INV-OF-+-SAME-ARG2
 (24 2 (:REWRITE MOD-WHEN-MULTIPLE))
 (24 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (20 4 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (12 4 (:REWRITE COMMUTATIVITY-OF-*))
 (9 4 (:REWRITE DEFAULT-+-2))
 (8 8 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (8 8 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (8 8 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (8 2 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::INTEGERP-OF-MINUS1-TYPE))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::<-OF-0--AND-MINUS1-TYPE))
 (6 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 2 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (6 2 (:REWRITE MOD-WHEN-<-OF-0))
 (6 2 (:REWRITE MOD-WHEN-<))
 (5 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (4 4 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 (2 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 )
(PFIELD::INV-OF--1
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (2 2 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (2 1 (:REWRITE EVENP-WHEN-PRIMEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (1 1 (:REWRITE NOT-EQUAL-OF-LEAST-DIVISOR-SAME-WHEN-DIVIDES))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )