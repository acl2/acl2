(LOGIOR-OF-SUM-WITH-NEGATIVE-OF-EXPT-HELPER
 (3616 64 (:REWRITE LOGIOR-AS-B-IOR))
 (2772 322 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (1827 113 (:REWRITE EQUAL-BIT-1))
 (1582 182 (:REWRITE LOGCAR-IDENTITY))
 (1456 87 (:REWRITE EQUAL-LOGCDR-CONSTANT-BRIDGE))
 (1341 322 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (1219 416 (:REWRITE UNSIGNED-BYTE-P-SUBTYPE))
 (806 26 (:REWRITE LOGCAR--))
 (610 610 (:REWRITE TOP-BIT-MEANS-<))
 (508 406 (:REWRITE DEFAULT-<-2))
 (508 82 (:REWRITE LOGCDR-EQUAL-0-REWRITE))
 (419 61 (:REWRITE LOGIOR-WHEN-J-IS-NOT-AN-INTEGERP))
 (408 406 (:REWRITE DEFAULT-<-1))
 (394 109 (:REWRITE EQUAL-1-HACK))
 (390 26 (:REWRITE LOGCAR-EXPT))
 (340 326 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (322 322 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (312 26 (:REWRITE ZP-OPEN))
 (307 264 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (277 192 (:REWRITE DEFAULT-+-1))
 (275 192 (:REWRITE DEFAULT-+-2))
 (262 97 (:REWRITE DEFAULT-UNARY-MINUS))
 (245 69 (:REWRITE EXPONENTS-ADD))
 (227 158 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (217 210 (:REWRITE LOGCDR-WHEN-I-IS-NOT-AN-INTEGERP))
 (187 180 (:REWRITE LOGCAR-WHEN-I-IS-NOT-AN-INTEGERP))
 (180 173 (:REWRITE EVENP-WHEN-NOT-INTEGERP))
 (157 65 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (135 45 (:REWRITE LOGCAR-0-REWRITE))
 (131 67 (:REWRITE DEFAULT-*-2))
 (128 2 (:REWRITE UNSIGNED-BYTE-P-1+))
 (121 21 (:LINEAR LOGIOR-BND-ERIC-LINEAR))
 (115 5 (:REWRITE UNSIGNED-BYTE-P--OF-MINUS))
 (102 26 (:REWRITE FALSIFY-UNSIGNED-BYTE-P))
 (99 61 (:REWRITE LOGIOR-WHEN-I-IS-NOT-AN-INTEGERP))
 (80 28 (:REWRITE FOLD-CONSTS-IN-+))
 (74 2 (:REWRITE UNSIGNED-BYTE-P-SHIFT-BY-CONSTANT-POWER-OF-2))
 (67 67 (:REWRITE DEFAULT-*-1))
 (59 31 (:REWRITE EQUAL-NEGATION-SAME-SIGN))
 (56 28 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (52 2 (:DEFINITION SIGNED-BYTE-P*))
 (50 33 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (43 43 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (42 2 (:REWRITE MOVE-NEGATED-TERM-TO-OTHER-SIDE-OF-<-TERM-1-ON-LHS))
 (28 4 (:REWRITE COMMUTATIVITY-OF-+))
 (27 27 (:REWRITE EQUAL-CONSTANT-+))
 (26 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-ADDING-BIG-POWER-OF-2-CONSTANT-VERSION))
 (21 1 (:REWRITE UNSIGNED-BYTE-P-+-EASY))
 (18 3 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT))
 (15 3 (:REWRITE BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P))
 (13 1 (:REWRITE 0-<-*))
 (9 9 (:REWRITE SBP-BOUND-1))
 (7 7 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (6 6 (:REWRITE EXPT-2-POSITIVE-RATIONAL-TYPE))
 (5 1 (:REWRITE LOGCDR-<-0))
 (4 4 (:REWRITE SIGNED-BYTE-P-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE SIGNED-BYTE-P-SUBTYPE))
 (4 4 (:REWRITE MOVE-NEGATED-TERM-TO-OTHER-SIDE-OF-<-TERM-1-ON-RHS))
 (3 3 (:TYPE-PRESCRIPTION POWER2P))
 (2 2 (:REWRITE EQUAL-LOGIOR-SINGLE-BIT))
 )
(LOGIOR-OF-SUM-WITH-NEGATIVE-OF-EXPT
 (58 1 (:REWRITE LOGIOR-WHEN-J-IS-NOT-AN-INTEGERP))
 (37 1 (:REWRITE LOGIOR-AS-B-IOR))
 (32 8 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (27 1 (:REWRITE INTEGERP-UNARY-))
 (21 1 (:REWRITE INTEGERP-+-MINUS-*-1))
 (20 3 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (12 8 (:REWRITE DEFAULT-<-2))
 (10 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE TOP-BIT-MEANS-<))
 (8 8 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (8 2 (:REWRITE INTEGERP-EXPT-1))
 (8 1 (:DEFINITION UNSIGNED-BYTE-P))
 (6 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 2 (:LINEAR LOGIOR-BND-ERIC-LINEAR))
 (6 1 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (6 1 (:LINEAR EXPT->-1))
 (5 5 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (5 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (5 1 (:REWRITE INTEGERP-*-1/2-EXPT))
 (5 1 (:DEFINITION INTEGER-RANGE-P))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (3 2 (:REWRITE INTEGERP-EXPT))
 (3 2 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (3 1 (:REWRITE DEFAULT-+-2))
 (3 1 (:REWRITE DEFAULT-*-2))
 (3 1 (:DEFINITION FIX))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (2 1 (:REWRITE LOGIOR-OF-SUM-WITH-NEGATIVE-OF-EXPT-HELPER))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE LOGIOR-WHEN-I-IS-NOT-AN-INTEGERP))
 (1 1 (:REWRITE INTEGERP-+-MINUS-*-4))
 (1 1 (:REWRITE INTEGER-RANGE-P-EXTEND-UPPER))
 (1 1 (:REWRITE INTEGER-RANGE-P-EXTEND-LOWER))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(LOGIOR-OF-SUM-WITH-NEGATIVE-OF-EXPT-ALT
 (173 173 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (124 24 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (119 5 (:REWRITE INTEGERP-UNARY-))
 (116 2 (:LINEAR LOGIOR-BND-ERIC-LINEAR))
 (85 5 (:REWRITE INTEGERP-+-MINUS-*-1))
 (81 3 (:REWRITE LOGIOR-WHEN-J-IS-NOT-AN-INTEGERP))
 (70 3 (:REWRITE LOGIOR-AS-B-IOR))
 (60 3 (:REWRITE LOGIOR-WHEN-I-IS-NOT-AN-INTEGERP))
 (38 4 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (33 9 (:REWRITE INTEGERP-EXPT-1))
 (20 4 (:REWRITE INTEGERP-*-1/2-EXPT))
 (19 12 (:REWRITE DEFAULT-<-2))
 (17 12 (:REWRITE DEFAULT-<-1))
 (16 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (15 5 (:DEFINITION FIX))
 (13 13 (:REWRITE TOP-BIT-MEANS-<))
 (13 13 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (13 9 (:REWRITE INTEGERP-EXPT))
 (12 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 4 (:REWRITE DEFAULT-*-2))
 (11 11 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (10 8 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (10 4 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-+-1))
 (7 1 (:REWRITE UNSIGNED-BYTE-P--OF-MINUS))
 (6 4 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (6 1 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (6 1 (:LINEAR EXPT->-1))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (4 4 (:REWRITE INTEGERP-+-MINUS-*-4))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE EQUAL-LOGIOR-SINGLE-BIT))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (1 1 (:REWRITE EXPT-2-POSITIVE-RATIONAL-TYPE))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(LOGIOR-OF-SUM-WITH-NEGATIVE-OF-EXPT-CONST-VERSION
 (16 2 (:REWRITE LOGIOR-AS-B-IOR))
 (13 3 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (12 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 1 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (10 1 (:LINEAR EXPT->-1))
 (9 6 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (7 3 (:REWRITE EXPT-EXPO-WHEN-POWER2P))
 (6 3 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (5 5 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (5 3 (:REWRITE DEFAULT-<-2))
 (4 4 (:TYPE-PRESCRIPTION POWER2P))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 3 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE LOGIOR-WHEN-I-IS-NOT-AN-INTEGERP))
 (4 2 (:LINEAR LOGIOR-BND-ERIC-LINEAR))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (3 3 (:REWRITE TOP-BIT-MEANS-<))
 (3 3 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (2 2 (:REWRITE LOGIOR-WHEN-J-IS-NOT-AN-INTEGERP))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (2 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (2 1 (:REWRITE EQUAL-NEGATION-SAME-SIGN))
 (1 1 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (1 1 (:REWRITE MOVE---TO-CONSTANT-IN-EQUAL))
 (1 1 (:REWRITE EQUAL-LOGIOR-SINGLE-BIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(UNSIGNED-BYTE-P-+-*4-BRIDGE
 (70 1 (:REWRITE UNSIGNED-BYTE-P-+-EASY))
 (56 56 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (49 2 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (26 2 (:LINEAR EXPT->-1))
 (16 3 (:REWRITE <-+-CONSTANT-CONSTANT))
 (12 2 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (10 10 (:REWRITE TOP-BIT-MEANS-<))
 (10 10 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (9 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (4 2 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (3 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (2 2 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (2 2 (:REWRITE EXPONENTS-ADD))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-ADDING-BIG-POWER-OF-2-CONSTANT-VERSION))
 (1 1 (:REWRITE SBP-BOUND-1))
 (1 1 (:REWRITE LOGHEAD-WHEN-SIZE-IS-NOT-POSITIVE))
 (1 1 (:REWRITE LOGHEAD-WHEN-SIZE-IS-NOT-AN-INTEGERP))
 (1 1 (:REWRITE LOGHEAD-WHEN-I-IS-NOT-AN-INTEGERP))
 (1 1 (:REWRITE LOGHEAD-SUBST2))
 (1 1 (:REWRITE LOGHEAD-SUBST))
 )
(UNSIGNED-BYTE-P-OF-X+1
 (172 16 (:REWRITE LOGHEAD-WHEN-SIZE-IS-NOT-POSITIVE))
 (95 16 (:REWRITE <-+-CONSTANT-CONSTANT))
 (86 51 (:REWRITE DEFAULT-+-2))
 (71 7 (:REWRITE EQUAL-BIT-1))
 (70 51 (:REWRITE DEFAULT-+-1))
 (55 55 (:REWRITE TOP-BIT-MEANS-<))
 (55 55 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (47 5 (:REWRITE FALSIFY-UNSIGNED-BYTE-P))
 (44 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-ADDING-BIG-POWER-OF-2-CONSTANT-VERSION))
 (42 39 (:REWRITE DEFAULT-<-2))
 (40 39 (:REWRITE DEFAULT-<-1))
 (38 32 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (37 37 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (32 16 (:REWRITE LOGHEAD-WHEN-SIZE-IS-NOT-AN-INTEGERP))
 (30 6 (:REWRITE EQUAL-1-HACK))
 (25 25 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (25 14 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (24 24 (:REWRITE LOGHEAD-SUBST2))
 (24 24 (:REWRITE LOGHEAD-SUBST))
 (22 16 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (19 1 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT))
 (19 1 (:REWRITE UNSIGNED-BYTE-P-+-EASY))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-SUBTYPE))
 (13 12 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (13 6 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (12 12 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (12 12 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (9 9 (:REWRITE LOGHEAD-OF-SUM-INTEGER-AND-NON-INTEGER))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 7 (:REWRITE EQUAL-CONSTANT-+))
 (7 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (6 6 (:REWRITE EQUAL-NEGATION-SAME-SIGN))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (5 5 (:REWRITE EXPONENTS-ADD))
 (5 1 (:REWRITE EXPT-2-EQUAL-1-REWRITE))
 (4 2 (:DEFINITION IFIX))
 (3 2 (:REWRITE IFIX-INTEGERP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE LOGCDR-WHEN-I-IS-NOT-AN-INTEGERP))
 (2 2 (:REWRITE EQUAL-LOGCDR-CONSTANT-BRIDGE))
 (2 2 (:LINEAR LOGHEAD-LEQ))
 (1 1 (:TYPE-PRESCRIPTION POWER2P))
 (1 1 (:DEFINITION =))
 )
(LOGBITP-TO-BOUND-WHEN-USB
 (374 374 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (173 1 (:REWRITE FLOOR-=-X/Y . 3))
 (96 4 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (78 42 (:REWRITE DEFAULT-<-2))
 (68 27 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (67 2 (:REWRITE RTL1))
 (67 2 (:REWRITE FLOOR-DETERMINED-1))
 (60 40 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (54 42 (:REWRITE DEFAULT-<-1))
 (54 2 (:REWRITE INTEGERP-+-MINUS-*-4))
 (49 49 (:REWRITE TOP-BIT-MEANS-<))
 (49 49 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (49 20 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (35 1 (:REWRITE FLOOR-=-X/Y . 2))
 (33 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (23 1 (:REWRITE EQUAL-1-HACK))
 (21 6 (:REWRITE DEFAULT-*-2))
 (20 1 (:REWRITE INTEGERP-OF-INVERSE-OF-EXPT))
 (19 1 (:REWRITE INTEGERP-/))
 (14 2 (:REWRITE DEFAULT-UNARY-/))
 (13 4 (:REWRITE FLOOR-WHEN-J-IS-NOT-AN-ACL2-NUMBERP))
 (12 2 (:REWRITE INTEGERP-EXPT-1))
 (12 2 (:REWRITE FLOOR-TYPE-3 . 3))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 2 (:REWRITE FLOOR-TYPE-4 . 2))
 (9 9 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (9 9 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (8 1 (:REWRITE EQUAL-BIT-1))
 (7 7 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (7 7 (:REWRITE EXPONENTS-ADD))
 (7 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-SUBTYPE))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 2 (:REWRITE INTEGERP-EXPT))
 (5 3 (:REWRITE INTEGERP-+-MINUS-*-2))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (4 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (4 1 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (3 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (2 2 (:REWRITE RATIONALP-+))
 (2 2 (:REWRITE FLOOR-TYPE-4 . 3))
 (2 2 (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
 (1 1 (:REWRITE SBP-BOUND-1))
 )
(LOGBIT-TO-BOUND-WHEN-USB
 (546 6 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (529 3 (:REWRITE LOGBITP-N-UNSIGNED-BYTE-P-N))
 (240 240 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (145 81 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (125 44 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER))
 (111 16 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (108 23 (:REWRITE <-+-CONSTANT-CONSTANT))
 (103 8 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (69 36 (:REWRITE DEFAULT-<-2))
 (68 4 (:REWRITE EXPT-IS-INCREASING-FOR-BASE>1))
 (61 36 (:REWRITE DEFAULT-<-1))
 (56 4 (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
 (53 53 (:REWRITE TOP-BIT-MEANS-<))
 (53 53 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (51 3 (:REWRITE LOGBITP-WHEN-I-IS-NOT-AN-INTEGERP))
 (50 5 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (50 5 (:LINEAR EXPT->-1))
 (46 46 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (46 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (43 22 (:DEFINITION FIX))
 (38 22 (:REWRITE INTEGERP-+-MINUS-*-2))
 (37 3 (:REWRITE LOGBITP-WHEN-I-IS-NON-POSITIVE))
 (34 34 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (26 2 (:REWRITE LOGBIT-WHEN-I-IS-NON-POSITIVE))
 (22 22 (:REWRITE INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (16 16 (:REWRITE RATIONALP-+))
 (10 10 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (9 6 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE SBP-BOUND-1))
 (7 7 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (7 7 (:REWRITE EXPONENTS-ADD))
 (6 6 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (4 4 (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
 (4 4 (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE<1))
 (3 3 (:REWRITE LOGBITP-WHEN-J-IS-NOT-AN-INTEGERP))
 (2 2 (:REWRITE LOGBIT-WHEN-I-IS-NOT-AN-INTEGERP))
 )
(SUM-POWER-OF-TWO-HELPER1
 (32 32 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (23 21 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (20 10 (:REWRITE DEFAULT-*-2))
 (11 11 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-+-1))
 (11 5 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (8 6 (:REWRITE EVENP-WHEN-NOT-INTEGERP))
 (7 7 (:REWRITE TOP-BIT-MEANS-<))
 (7 7 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (7 7 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (7 7 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-SUBTYPE))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (4 2 (:REWRITE ODD-EQUAL-EXPT-CHEAP))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (2 2 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(SUM-POWER-OF-TWO
 (614 5 (:REWRITE LOGBITP-N-UNSIGNED-BYTE-P-N))
 (413 9 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (210 5 (:REWRITE <-*-/-LEFT-COMMUTED))
 (94 24 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (85 25 (:REWRITE <-+-CONSTANT-CONSTANT))
 (75 5 (:REWRITE COLLECT-CONSTANTS-+-LEMMA))
 (73 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (68 61 (:REWRITE DEFAULT-+-2))
 (65 60 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (65 5 (:REWRITE LOGBITP-WHEN-I-IS-NON-POSITIVE))
 (63 61 (:REWRITE DEFAULT-+-1))
 (47 36 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (46 11 (:REWRITE EXPONENTS-ADD))
 (43 43 (:REWRITE TOP-BIT-MEANS-<))
 (42 42 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (37 22 (:REWRITE DEFAULT-<-1))
 (33 23 (:REWRITE DEFAULT-*-2))
 (24 22 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE DEFAULT-*-1))
 (18 18 (:REWRITE INTEGER-LENGTH-WHEN-I-IS-NOT-AN-INTEGERP))
 (14 12 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (10 5 (:REWRITE LOGBITP-WHEN-I-IS-NOT-AN-INTEGERP))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (8 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (5 5 (:REWRITE SBP-BOUND-1))
 (5 5 (:REWRITE LOGBITP-WHEN-J-IS-NOT-AN-INTEGERP))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE ODD-EQUAL-EXPT-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION EVENP))
 (2 2 (:REWRITE EQUAL-CONSTANT-+))
 )
(SUM-POWER-OF-TWO-HELPER2
 (121 121 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (54 1 (:REWRITE EQUAL-LOGCDR-CONSTANT-BRIDGE))
 (44 8 (:REWRITE FALSIFY-UNSIGNED-BYTE-P))
 (32 2 (:LINEAR LOGCAR-RANGE-LINEAR))
 (27 27 (:REWRITE TOP-BIT-MEANS-<))
 (27 27 (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
 (27 3 (:REWRITE LOGCAR-IDENTITY))
 (25 21 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (24 4 (:REWRITE <-+-CONSTANT-CONSTANT))
 (23 18 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (22 22 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (22 12 (:REWRITE DEFAULT-*-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (19 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-SUBTYPE))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (14 14 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (14 14 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (13 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (12 12 (:REWRITE DEFAULT-*-1))
 (12 3 (:REWRITE LOGCAR-EVENP))
 (11 11 (:TYPE-PRESCRIPTION EVENP))
 (9 1 (:REWRITE EQUAL-BIT-1))
 (8 4 (:REWRITE ODD-EQUAL-EXPT-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION LOGCAR-TYPE))
 (5 5 (:REWRITE LOGCDR-WHEN-I-IS-NOT-AN-INTEGERP))
 (5 1 (:REWRITE EQUAL-1-HACK))
 (4 4 (:REWRITE EVENP-WHEN-NOT-INTEGERP))
 (4 4 (:REWRITE COMBINE-CONSTANTS-IN-EQUAL-OF-TIMES))
 (3 3 (:REWRITE LOGCAR-WHEN-I-IS-NOT-AN-INTEGERP))
 (3 3 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (3 1 (:REWRITE LOGCAR-0-REWRITE))
 (2 2 (:REWRITE SUM-POWER-OF-TWO))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE EQUAL-CONSTANT-+))
 )
(SUM-POWER-OF-TWO-1
 (928 10 (:REWRITE LOGBITP-N-UNSIGNED-BYTE-P-N))
 (565 16 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-TWO))
 (238 7 (:REWRITE <-*-/-LEFT-COMMUTED))
 (135 27 (:REWRITE <-+-CONSTANT-CONSTANT))
 (135 9 (:REWRITE COLLECT-CONSTANTS-+-LEMMA))
 (131 16 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NON-POSITIVE))
 (130 32 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (118 10 (:REWRITE LOGBITP-WHEN-I-IS-NON-POSITIVE))
 (105 98 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (86 72 (:REWRITE DEFAULT-+-2))
 (86 64 (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
 (75 75 (:REWRITE TOP-BIT-MEANS-<))
 (74 74 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
 (72 72 (:REWRITE DEFAULT-+-1))
 (63 40 (:REWRITE DEFAULT-<-1))
 (44 40 (:REWRITE DEFAULT-<-2))
 (42 24 (:REWRITE DEFAULT-*-2))
 (41 35 (:REWRITE INTEGER-LENGTH-WHEN-I-IS-NOT-AN-INTEGERP))
 (24 24 (:REWRITE DEFAULT-*-1))
 (20 10 (:REWRITE LOGBITP-WHEN-I-IS-NOT-AN-INTEGERP))
 (18 16 (:LINEAR EXPT-LESS-THAN-1-HACK))
 (18 8 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-REWRITES-TO-LOWER-BOUND-WHEN-WE-KNOW-UPPER-BOUND-ONE))
 (16 16 (:REWRITE UNSIGNED-BYTE-P-OF-EXPT-CONST-VERSION))
 (14 7 (:REWRITE UNSIGNED-BYTE-P-WHEN-N-IS-NOT-AN-INTEGERP))
 (10 10 (:REWRITE LOGBITP-WHEN-J-IS-NOT-AN-INTEGERP))
 (10 5 (:REWRITE ODD-EQUAL-EXPT-CHEAP))
 (9 9 (:REWRITE SBP-BOUND-1))
 (6 6 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
 (5 5 (:TYPE-PRESCRIPTION EVENP))
 (3 3 (:REWRITE SUM-POWER-OF-TWO))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 (3 3 (:REWRITE COMBINE-CONSTANTS-IN-EQUAL-OF-TIMES))
 )
