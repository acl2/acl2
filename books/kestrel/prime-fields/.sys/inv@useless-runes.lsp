(PFIELD::INV
 (64 5 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (33 5 (:REWRITE MOD-WHEN-<-OF-0))
 (21 11 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (20 20 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (19 5 (:REWRITE COMMUTATIVITY-OF-*))
 (18 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (14 10 (:REWRITE DEFAULT-*-2))
 (14 10 (:REWRITE DEFAULT-*-1))
 (13 13 (:TYPE-PRESCRIPTION PFIELD::<-OF-0--AND-MINUS1-TYPE))
 (11 11 (:REWRITE DEFAULT-<-2))
 (9 5 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (8 4 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (8 4 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (8 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (5 5 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (5 5 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 )
(PFIELD::NATP-OF-INV)
(PFIELD::FEP-OF-INV
 (65 7 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (21 7 (:REWRITE MOD-WHEN-<-OF-0))
 (21 7 (:REWRITE COMMUTATIVITY-OF-*))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (16 7 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (15 5 (:REWRITE MOD-WHEN-<))
 (14 14 (:REWRITE DEFAULT-*-2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (12 12 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (7 7 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (7 7 (:REWRITE DEFAULT-UNARY-/))
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
 (37 37 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (32 14 (:REWRITE MOD-WHEN-<-OF-0))
 (22 8 (:REWRITE MOD-WHEN-<))
 (19 19 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 (16 4 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (14 14 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (9 9 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (8 8 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
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
 (150 50 (:REWRITE MOD-WHEN-<-OF-0))
 (150 50 (:REWRITE COMMUTATIVITY-OF-*))
 (126 42 (:REWRITE MOD-WHEN-<))
 (119 119 (:REWRITE DEFAULT-<-2))
 (119 119 (:REWRITE DEFAULT-<-1))
 (100 100 (:REWRITE DEFAULT-*-2))
 (100 100 (:REWRITE DEFAULT-*-1))
 (80 50 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (64 64 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (60 20 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (50 50 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (42 42 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (33 9 (:REWRITE PFIELD::POW-OF-+))
 (30 30 (:REWRITE DEFAULT-UNARY-/))
 (23 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (20 20 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 (19 19 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (14 10 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (14 10 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (12 3 (:REWRITE PFIELD::EQUAL-OF-0-AND-MUL))
 (11 11 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (10 10 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (10 10 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 (9 3 (:REWRITE PFIELD::EQUAL-OF-0-AND-MUL-GEN))
 (6 6 (:TYPE-PRESCRIPTION DM::PRIMEP))
 )
(PFIELD::INV-OF-+-SAME-ARG1
 (60 14 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (58 58 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (58 58 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (53 53 (:REWRITE DEFAULT-<-2))
 (53 53 (:REWRITE DEFAULT-<-1))
 (42 14 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (42 14 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (24 8 (:REWRITE MOD-WHEN-<-OF-0))
 (11 11 (:REWRITE DEFAULT-*-2))
 (11 11 (:REWRITE DEFAULT-*-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (9 9 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (9 3 (:REWRITE MOD-WHEN-<))
 (8 8 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (8 8 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (8 2 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (7 7 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (3 3 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (3 3 (:REWRITE INVERSE-OF-*))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 )
(PFIELD::INV-OF-+-SAME-ARG2
 (24 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (10 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (9 4 (:REWRITE DEFAULT-+-2))
 (8 8 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (8 2 (:REWRITE PFIELD::FEP-FIX-WHEN-FEP))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::INTEGERP-OF-MINUS1-TYPE))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::<-OF-0--AND-MINUS1-TYPE))
 (6 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 2 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (6 2 (:REWRITE MOD-WHEN-<-OF-0))
 (6 2 (:REWRITE MOD-WHEN-<))
 (6 2 (:REWRITE COMMUTATIVITY-OF-*))
 (5 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 (2 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
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
 (1 1 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(PFIELD::NOT-EQUAL-OF-INV-AND-0
 (8 2 (:REWRITE PFIELD::POW-OF-+))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::INTEGERP-OF-MINUS1-TYPE))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::<-OF-0--AND-MINUS1-TYPE))
 (6 3 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (6 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 2 (:REWRITE PFIELD::POW-WHEN-<-OF-0-ARG2-CHEAP))
 (6 2 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (3 3 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (3 3 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE PFIELD::POW-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::POW-SUBST-WHEN-EQUAL-OF-MOD))
 (2 2 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (1 1 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(PFIELD::MUL-OF-MUL-OF-INV
 (50 4 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (18 4 (:REWRITE MOD-WHEN-<-OF-0))
 (12 9 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (12 9 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (10 5 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (9 9 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (9 9 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (9 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (8 6 (:REWRITE DEFAULT-*-2))
 (8 6 (:REWRITE DEFAULT-*-1))
 (8 4 (:REWRITE DEFAULT-UNARY-/))
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (7 5 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-*))
 (4 4 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (4 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (4 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (4 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (3 3 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-INV))
 (3 3 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (3 3 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(PFIELD::MUL-OF-INV-ARG1
 (19 19 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 )
(PFIELD::MUL-OF-INV-MUL-OF-INV
 (15 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (4 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (4 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 1 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (3 3 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE COMMUTATIVITY-OF-*))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (1 1 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (1 1 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-INV))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (1 1 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (1 1 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 )
(PFIELD::EQUAL-OF-INV
 (51 3 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (15 3 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (12 3 (:REWRITE COMMUTATIVITY-OF-*))
 (11 7 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (10 10 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (9 6 (:REWRITE DEFAULT-*-2))
 (9 6 (:REWRITE DEFAULT-*-1))
 (8 7 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (6 6 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (6 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (6 3 (:REWRITE MOD-WHEN-<-OF-0))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (3 3 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (3 3 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (1 1 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 )
(PFIELD::INV-OF-INV
 (4 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (2 2 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE MOD-WHEN-<-OF-0))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
