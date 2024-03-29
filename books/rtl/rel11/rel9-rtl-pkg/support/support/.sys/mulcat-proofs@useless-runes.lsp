(RTL::BVECP)
(RTL::FL)
(RTL::BITS)
(RTL::BITN)
(RTL::MULCAT
 (5 5 (:TYPE-PRESCRIPTION RTL::NONNEG-+-TYPE))
 )
(RTL::MULCAT-NONNEGATIVE-INTEGER-TYPE)
(RTL::MULCAT-1
 (632 11 (:REWRITE RTL::BITS-SPLIT-AROUND-ZERO))
 (285 19 (:REWRITE RTL::BVECP-WITH-N-NOT-A-POSITIVE-INTEGER))
 (250 25 (:LINEAR RTL::EXPT-WITH-SMALL-N))
 (224 11 (:REWRITE RTL::BITS-TAIL))
 (209 11 (:REWRITE RTL::BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (187 122 (:REWRITE DEFAULT-<-2))
 (148 122 (:REWRITE DEFAULT-<-1))
 (139 139 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (139 139 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (139 139 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (139 139 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (139 139 (:REWRITE RTL::EXPT-COMPARE))
 (139 139 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (122 122 (:META CANCEL_PLUS-LESSP-CORRECT))
 (115 6 (:LINEAR RTL::BITS-LESS-THAN-X-GEN))
 (114 91 (:REWRITE DEFAULT-+-1))
 (112 6 (:LINEAR RTL::BITS-LESS-THAN-X))
 (110 11 (:REWRITE RTL::BITS-FORCE-WITH-A-CHOSEN-NEG))
 (103 91 (:REWRITE DEFAULT-+-2))
 (99 33 (:TYPE-PRESCRIPTION RTL::INTEGERP-PROD))
 (66 66 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER))
 (66 66 (:REWRITE RTL::EXPT-EXECUTE-REWRITE))
 (66 66 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (55 11 (:REWRITE A2))
 (50 50 (:LINEAR RTL::EXPT-EXCEEDS-2))
 (36 18 (:REWRITE RTL::BITS-WITH-I-NOT-AN-INTEGER-2))
 (35 13 (:REWRITE DEFAULT-*-2))
 (29 29 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (26 26 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (22 11 (:REWRITE RTL::BITS-WITH-I-NOT-AN-INTEGER))
 (19 19 (:REWRITE RTL::BVECP-LONGER))
 (18 18 (:REWRITE RTL::BITS-WITH-J-NOT-AN-INTEGER-2))
 (18 18 (:REWRITE RTL::BITS-EXPT-CONSTANT))
 (13 13 (:REWRITE DEFAULT-*-1))
 (11 11 (:REWRITE RTL::BITS-WITH-X-NOT-RATIONAL))
 (11 11 (:REWRITE RTL::BITS-WITH-J-NOT-AN-INTEGER))
 (11 11 (:REWRITE RTL::BITS-WITH-BAD-INDEX-2))
 (11 11 (:REWRITE RTL::BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
 (8 8 (:REWRITE RTL::POWER2-INTEGER))
 (8 8 (:REWRITE RTL::INTEGERP-MINUS))
 (6 6 (:REWRITE RTL::NONNEG-+))
 (6 2 (:REWRITE RTL::BVECP-OF-NON-INTEGER))
 (3 1 (:REWRITE RTL::INTEGERP-IMPLIES-NOT-COMPLEX-RATIONALP))
 (2 2 (:REWRITE RTL::CAT-WITH-N-NOT-A-NATURAL))
 (2 2 (:REWRITE RTL::CAT-WITH-M-NOT-A-NATURAL))
 (2 2 (:REWRITE RTL::CAT-TIGHTEN-X))
 (1 1 (:REWRITE RTL::EXPT-COMPARE-EQUAL))
 (1 1 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (1 1 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (1 1 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (1 1 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (1 1 (:REWRITE RTL::BITS-MATCH))
 (1 1 (:REWRITE RTL::BITS-EQUAL-IMPOSSIBLE-CONSTANT))
 (1 1 (:REWRITE RTL::BITS-DONT-MATCH))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(RTL::MULCAT-BVECP-SIMPLE
 (470 4 (:REWRITE RTL::CAT-WITH-M-NOT-A-NATURAL))
 (352 5 (:REWRITE RTL::REARRANGE-NEGATIVE-COEFS-<))
 (245 4 (:REWRITE RTL::BVECP-WITH-N-NOT-A-POSITIVE-INTEGER))
 (238 58 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (117 3 (:REWRITE RTL::PRODUCT-GREATER-THAN-ZERO-2))
 (57 52 (:REWRITE DEFAULT-*-2))
 (53 53 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (53 53 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (53 53 (:REWRITE RTL::EXPT-COMPARE))
 (52 52 (:REWRITE DEFAULT-*-1))
 (49 49 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (49 49 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (46 43 (:REWRITE DEFAULT-<-2))
 (46 43 (:REWRITE DEFAULT-<-1))
 (43 43 (:META CANCEL_PLUS-LESSP-CORRECT))
 (39 4 (:REWRITE RTL::CAT-TIGHTEN-X))
 (36 27 (:REWRITE DEFAULT-+-1))
 (35 27 (:REWRITE DEFAULT-+-2))
 (25 5 (:REWRITE RTL::COMMUTATIVITY-2-OF-*))
 (21 21 (:REWRITE RTL::POWER2-INTEGER))
 (21 21 (:REWRITE RTL::INTEGERP-MINUS))
 (21 20 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (20 20 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (20 20 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (20 20 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (19 1 (:REWRITE RTL::COLLECT-ANOTHER))
 (12 6 (:REWRITE RTL::INTEGERP-PROD))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-UNARY-/))
 (10 6 (:REWRITE RTL::BVECP-OF-NON-INTEGER))
 (10 5 (:REWRITE UNICITY-OF-1))
 (10 5 (:REWRITE RTL::INVERSE-OF-*-2))
 (6 6 (:REWRITE RTL::BVECP-LONGER))
 (5 5 (:REWRITE RTL::EXPT-COMPARE-EQUAL))
 (5 5 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (5 5 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (5 5 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (5 5 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (5 5 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (5 5 (:REWRITE RTL::A8))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:TYPE-PRESCRIPTION RTL::MULCAT-NONNEGATIVE-INTEGER-TYPE))
 (4 4 (:REWRITE RTL::CAT-WITH-N-NOT-A-NATURAL))
 (1 1 (:REWRITE RTL::DUMB))
 (1 1 (:REWRITE RTL::CAT-BVECP-REWRITE-CONSTANTS))
 (1 1 (:REWRITE RTL::A4))
 )
(RTL::MULCAT-BVECP
 (60 60 (:TYPE-PRESCRIPTION RTL::INTEGERP-PROD))
 (59 1 (:REWRITE RTL::BVECP-WITH-N-NOT-A-POSITIVE-INTEGER))
 (39 1 (:REWRITE RTL::PRODUCT-GREATER-THAN-ZERO-2))
 (12 2 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (12 2 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 2))
 (9 6 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (7 7 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (7 7 (:REWRITE RTL::EXPT-COMPARE))
 (7 7 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (7 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (6 6 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE RTL::INTEGERP-PROD))
 (3 3 (:REWRITE RTL::POWER2-INTEGER))
 (3 3 (:REWRITE RTL::INTEGERP-MINUS))
 (2 2 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (2 2 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 1))
 (2 2 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (2 2 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (2 2 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 2))
 (2 2 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 1))
 (2 1 (:REWRITE DEFAULT-*-2))
 (2 1 (:REWRITE RTL::BVECP-OF-NON-INTEGER))
 (1 1 (:TYPE-PRESCRIPTION RTL::MULCAT-NONNEGATIVE-INTEGER-TYPE))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(RTL::MULCAT-0
 (276 156 (:REWRITE DEFAULT-*-2))
 (171 77 (:REWRITE RTL::INTEGERP-MINUS))
 (164 164 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (164 164 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (164 164 (:REWRITE RTL::EXPT-COMPARE))
 (157 157 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (157 157 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (155 137 (:REWRITE DEFAULT-<-1))
 (153 24 (:REWRITE RTL::INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER))
 (143 137 (:REWRITE DEFAULT-<-2))
 (138 1 (:REWRITE RTL::CAT-EQUAL-Y-SPECIAL))
 (137 137 (:META CANCEL_PLUS-LESSP-CORRECT))
 (129 1 (:REWRITE RTL::CAT-EQUAL-Y))
 (114 1 (:REWRITE RTL::CAT-0))
 (111 1 (:REWRITE RTL::CAT-EQUAL-Y-ALT))
 (108 50 (:REWRITE RTL::A5))
 (108 13 (:REWRITE RTL::INTEGERP-+))
 (101 76 (:REWRITE DEFAULT-+-1))
 (98 80 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (95 76 (:REWRITE DEFAULT-+-2))
 (89 8 (:REWRITE RTL::NONNEG-+))
 (87 6 (:REWRITE RTL::PRODUCT-LESS-THAN-ZERO))
 (80 80 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (80 80 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (80 80 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 1))
 (78 78 (:REWRITE RTL::POWER2-INTEGER))
 (47 47 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (38 18 (:REWRITE RTL::INTEGERP-PROD))
 (37 1 (:REWRITE RTL::PRODUCT-GREATER-THAN-ZERO-2))
 (25 25 (:REWRITE RTL::EXPT-COMPARE-EQUAL))
 (25 25 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (25 25 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (25 25 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (25 25 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (25 25 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (25 25 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (25 25 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (22 22 (:REWRITE DEFAULT-UNARY-/))
 (20 2 (:DEFINITION NATP))
 (18 1 (:REWRITE RTL::CAT-EQUAL-0))
 (18 1 (:REWRITE RTL::CAT-CONSTANT-EQUAL-CONSTANT-HACK))
 (15 15 (:REWRITE RTL::CAT-TIGHTEN-X))
 (13 13 (:REWRITE RTL::INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (12 6 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER))
 (8 8 (:REWRITE RTL::BVECP-LONGER))
 (7 6 (:LINEAR RTL::EXPT-EXCEEDS-2))
 (6 6 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (6 6 (:REWRITE RTL::EXPT-EXECUTE-REWRITE))
 (6 6 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (3 3 (:REWRITE RTL::BITS-WITH-J-NOT-AN-INTEGER-2))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE RTL::BITS-EXPT-CONSTANT))
 (1 1 (:REWRITE RTL::EVEN-ODD-5))
 (1 1 (:REWRITE RTL::CAT-EQUAL-CONSTANT))
 )
(RTL::MULCAT-0-TWO)
(RTL::BVECP-MULCAT-1
 (1 1 (:REWRITE RTL::POWER2-INTEGER))
 (1 1 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (1 1 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (1 1 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (1 1 (:REWRITE RTL::INTEGERP-MINUS))
 (1 1 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (1 1 (:REWRITE RTL::EXPT-COMPARE))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(RTL::MULCAT-N-1-1
 (124 3 (:REWRITE RTL::BITS-REDUCE))
 (60 6 (:REWRITE RTL::COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (42 3 (:REWRITE RTL::CAT-WITH-M-NOT-A-NATURAL))
 (41 31 (:REWRITE DEFAULT-+-2))
 (37 31 (:REWRITE DEFAULT-+-1))
 (27 12 (:TYPE-PRESCRIPTION RTL::A14 . 2))
 (25 12 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (18 18 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (18 18 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (18 18 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (18 18 (:REWRITE RTL::EXPT-COMPARE))
 (18 18 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (16 11 (:REWRITE DEFAULT-*-2))
 (15 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:TYPE-PRESCRIPTION RTL::A14 . 1))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (11 11 (:REWRITE DEFAULT-*-1))
 (9 9 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-RATIONAL-TYPE))
 (9 9 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (6 3 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER))
 (6 3 (:REWRITE RTL::BITS-WITH-I-NOT-AN-INTEGER-2))
 (3 3 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (3 3 (:REWRITE RTL::CAT-WITH-N-NOT-A-NATURAL))
 (3 3 (:REWRITE RTL::CAT-TIGHTEN-X))
 (3 3 (:REWRITE RTL::BITS-WITH-J-NOT-AN-INTEGER-2))
 (3 3 (:REWRITE RTL::BITS-EXPT-CONSTANT))
 (2 2 (:REWRITE RTL::NONNEG-+))
 (1 1 (:REWRITE RTL::POWER2-INTEGER))
 (1 1 (:REWRITE RTL::INTEGERP-MINUS))
 (1 1 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER-SPECIAL))
 )
(RTL::MULCAT-N-1
 (64 6 (:LINEAR RTL::EXPT-WITH-SMALL-N))
 (31 19 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE RTL::POWER2-INTEGER))
 (23 23 (:REWRITE RTL::INTEGERP-MINUS))
 (21 16 (:REWRITE DEFAULT-<-1))
 (20 19 (:REWRITE DEFAULT-+-1))
 (20 16 (:REWRITE DEFAULT-<-2))
 (20 4 (:DEFINITION NATP))
 (17 17 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (17 17 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (17 17 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (17 17 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (17 17 (:REWRITE RTL::EXPT-COMPARE))
 (17 17 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (16 16 (:META CANCEL_PLUS-LESSP-CORRECT))
 (15 15 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (15 9 (:REWRITE DEFAULT-*-2))
 (14 14 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (13 9 (:REWRITE DEFAULT-*-1))
 (10 1 (:REWRITE RTL::COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 3 (:REWRITE RTL::EXPT-2-IS-NOT-ODD))
 (8 8 (:REWRITE RTL::COLLECT-CONSTANTS-IN-EQUAL-OF-SUMS))
 (7 7 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION EVENP))
 (6 3 (:REWRITE UNICITY-OF-1))
 (6 3 (:REWRITE RTL::CAT-WITH-M-NOT-A-NATURAL))
 (5 5 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER-SPECIAL))
 (4 4 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 3 (:REWRITE RTL::CAT-WITH-N-NOT-A-NATURAL))
 (3 3 (:REWRITE RTL::CAT-TIGHTEN-X))
 (1 1 (:REWRITE RTL::EXPO-SHIFT-GENERAL))
 (1 1 (:REWRITE RTL::COLLECT-CONSTANTS-WITH-DIVISION))
 )
(RTL::MULCAT-INDUCT
 (6 6 (:TYPE-PRESCRIPTION RTL::NONNEG-+-TYPE))
 )
(RTL::BITN-MULCAT-1
 (128 8 (:REWRITE RTL::BVECP-TIGHTEN))
 (127 8 (:REWRITE RTL::BITN-TOO-SMALL))
 (111 111 (:TYPE-PRESCRIPTION RTL::NONNEG-+-TYPE))
 (78 5 (:REWRITE RTL::BVECP+1))
 (77 8 (:REWRITE RTL::BITN-KNOWN-NOT-0-REPLACE-WITH-1))
 (68 7 (:REWRITE RTL::CAT-WITH-M-NOT-A-NATURAL))
 (60 6 (:REWRITE RTL::COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (49 33 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (33 33 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (33 33 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (33 33 (:REWRITE RTL::EXPT-COMPARE))
 (33 33 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (32 32 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (32 31 (:REWRITE DEFAULT-+-1))
 (31 31 (:REWRITE DEFAULT-+-2))
 (31 25 (:REWRITE DEFAULT-<-2))
 (28 25 (:REWRITE DEFAULT-<-1))
 (27 3 (:REWRITE RTL::BVECP-0-THM))
 (25 25 (:META CANCEL_PLUS-LESSP-CORRECT))
 (16 1 (:LINEAR RTL::BITN-UPPER-BOUND-LINEAR))
 (12 12 (:REWRITE RTL::BITS-0-MEANS-TOP-BIT-0))
 (10 5 (:REWRITE RTL::BITN-WITH-N-NOT-AN-INTEGER))
 (10 5 (:REWRITE RTL::BITN-OF-NON-RATIONAL))
 (9 1 (:REWRITE RTL::BITN-SPLIT-AROUND-ZERO))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE RTL::BITN-BVECP-0-ERIC))
 (7 7 (:REWRITE RTL::EXPT-COMPARE-EQUAL))
 (7 7 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (7 7 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (7 7 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (7 7 (:REWRITE RTL::CAT-WITH-N-NOT-A-NATURAL))
 (7 7 (:REWRITE RTL::CAT-TIGHTEN-X))
 (7 7 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7 3 (:REWRITE RTL::BVECP-OF-NON-INTEGER))
 (6 6 (:REWRITE RTL::POWER2-INTEGER))
 (6 6 (:REWRITE RTL::INTEGERP-MINUS))
 (6 6 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (5 5 (:REWRITE RTL::EXPT-EXECUTE-REWRITE))
 (5 5 (:REWRITE RTL::BITN-MINUS))
 (4 4 (:REWRITE RTL::BVECP-WITH-N-NOT-A-POSITIVE-INTEGER))
 (4 2 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER))
 (3 3 (:TYPE-PRESCRIPTION RTL::INTEGERP-PROD))
 (3 3 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER-SPECIAL))
 (3 1 (:REWRITE COMMUTATIVITY-OF-*))
 (2 2 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (2 2 (:REWRITE RTL::BITN-EQUAL-TO-SILLY-VALUE))
 (2 2 (:REWRITE RTL::BITN-CAT-CONSTANTS))
 (1 1 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-RATIONAL-TYPE))
 (1 1 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (1 1 (:REWRITE RTL::UNARY-DIVIDE-GREATER-THAN-NON-ZERO-CONSTANT))
 (1 1 (:REWRITE RTL::BITN-OF-EXPT-EQUAL-0))
 )
(RTL::BITN-MULCAT-2
 (119 5 (:REWRITE RTL::BITN-TOO-SMALL))
 (66 66 (:REWRITE DEFAULT-*-2))
 (66 66 (:REWRITE DEFAULT-*-1))
 (48 1 (:REWRITE RTL::BVECP-TIGHTEN))
 (36 36 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (36 36 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (36 36 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (36 36 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (36 36 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 2))
 (36 36 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 1))
 (15 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (7 1 (:REWRITE RTL::BITN-SPLIT-AROUND-ZERO))
 (5 5 (:TYPE-PRESCRIPTION RTL::NONNEG-+-TYPE))
 (5 5 (:REWRITE RTL::BITS-0-MEANS-TOP-BIT-0))
 (5 5 (:REWRITE RTL::BITN-BVECP-0-ERIC))
 (5 4 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER))
 (4 4 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-RATIONAL-TYPE))
 (4 4 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (4 4 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (4 4 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (4 4 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (4 4 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (4 4 (:REWRITE RTL::EXPT-EXECUTE-REWRITE))
 (4 4 (:REWRITE RTL::EXPT-COMPARE))
 (4 4 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (4 4 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-<))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:REWRITE RTL::BITN-OF-NON-RATIONAL))
 (2 2 (:REWRITE RTL::EXPT-COMPARE-EQUAL))
 (2 2 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (2 2 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (2 2 (:REWRITE RTL::BITN-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE RTL::BITN-MINUS))
 (2 2 (:REWRITE RTL::BITN-EQUAL-TO-SILLY-VALUE))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER-SPECIAL))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (1 1 (:REWRITE RTL::BITN-OF-EXPT-EQUAL-1))
 (1 1 (:REWRITE RTL::BITN-OF-EXPT-EQUAL-0))
 )
(RTL::MULCAT-BITS
 (3788 40 (:REWRITE RTL::BITS-REDUCE-EXACTP))
 (2621 20 (:REWRITE RTL::EXPO-UNIQUE-ERIC-2))
 (2026 36 (:REWRITE RTL::BVECP-TIGHTEN))
 (1356 38 (:REWRITE RTL::BITN-TOO-SMALL))
 (1179 25 (:REWRITE RTL::BITS-SPLIT-AROUND-ZERO))
 (841 58 (:LINEAR RTL::EXPT-WITH-SMALL-N))
 (705 41 (:REWRITE RTL::MOVE-NEGATIVE-CONSTANT-1))
 (694 369 (:REWRITE DEFAULT-<-2))
 (573 454 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (464 447 (:REWRITE RTL::EXPT-COMPARE))
 (454 454 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (444 444 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (444 444 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (389 369 (:REWRITE DEFAULT-<-1))
 (383 78 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 1))
 (372 372 (:META CANCEL_PLUS-LESSP-CORRECT))
 (339 303 (:TYPE-PRESCRIPTION RTL::EXPO-OF-INTEGER-TYPE))
 (325 325 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-RATIONAL-TYPE))
 (325 325 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (320 244 (:REWRITE DEFAULT-+-2))
 (315 244 (:REWRITE DEFAULT-+-1))
 (307 6 (:LINEAR RTL::BITN-UPPER-BOUND-LINEAR))
 (274 212 (:REWRITE DEFAULT-*-2))
 (232 5 (:REWRITE RTL::BITN-SPLIT-AROUND-ZERO))
 (231 2 (:REWRITE RTL::BITN-BITS-GEN))
 (214 25 (:REWRITE RTL::BITS-FORCE-WITH-A-CHOSEN-NEG))
 (212 212 (:REWRITE DEFAULT-*-1))
 (210 38 (:REWRITE RTL::BITN-KNOWN-NOT-0-REPLACE-WITH-1))
 (182 14 (:DEFINITION ABS))
 (170 1 (:REWRITE RTL::EXPO-BITS-WHEN-TOP-BIT-IS-1))
 (158 88 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER))
 (149 29 (:REWRITE A2))
 (148 20 (:REWRITE RTL::ABS-POS))
 (132 3 (:LINEAR RTL::BITS-LESS-THAN-X-GEN))
 (132 3 (:LINEAR RTL::BITS-LESS-THAN-X))
 (131 1 (:REWRITE RTL::BITS-UPPER-BOUND-2))
 (118 78 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 2))
 (118 2 (:REWRITE RTL::BITN-MULCAT-2))
 (116 116 (:LINEAR RTL::EXPT-EXCEEDS-2))
 (103 103 (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
 (103 103 (:REWRITE RTL::EXPT-EXECUTE-REWRITE))
 (94 78 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 2))
 (93 93 (:REWRITE RTL::EXPT-COMPARE-EQUAL))
 (93 93 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL))
 (92 1 (:REWRITE RTL::REARRANGE-NEGATIVE-COEFS-EQUAL))
 (88 88 (:REWRITE RTL::EXPT-2-EVALUATOR))
 (82 82 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (78 78 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (78 78 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (78 78 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 1))
 (77 68 (:REWRITE RTL::EXPT-WITH-I-NON-INTEGER-SPECIAL))
 (76 40 (:REWRITE RTL::BITS-WITH-I-NOT-AN-INTEGER-2))
 (73 73 (:REWRITE RTL::EQUAL-OF-PREDS-REWRITE))
 (73 73 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (73 73 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (72 72 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (72 72 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (50 50 (:REWRITE DEFAULT-UNARY-/))
 (48 48 (:REWRITE RTL::POWER2-INTEGER))
 (48 48 (:REWRITE RTL::INTEGERP-MINUS))
 (48 16 (:REWRITE RTL::NONNEG-+))
 (45 27 (:REWRITE RTL::BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
 (41 41 (:REWRITE RTL::CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (40 40 (:REWRITE RTL::COLLECT-CONSTANTS-IN-EQUAL-OF-SUMS))
 (40 40 (:REWRITE RTL::BITS-WITH-J-NOT-AN-INTEGER-2))
 (40 40 (:REWRITE RTL::BITS-EXPT-CONSTANT))
 (40 40 (:REWRITE RTL::BITS-0-MEANS-TOP-BIT-0))
 (38 38 (:REWRITE RTL::BITN-BVECP-0-ERIC))
 (28 28 (:REWRITE RTL::BVECP-LONGER))
 (25 25 (:REWRITE RTL::BITS-WITH-BAD-INDEX-2))
 (24 12 (:REWRITE RTL::BITN-WITH-N-NOT-AN-INTEGER))
 (22 22 (:REWRITE RTL::EXPO-SHIFT-GENERAL))
 (22 20 (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (22 20 (:REWRITE RTL::EXPO-OF-NOT-RATIONALP))
 (21 21 (:REWRITE RTL::CAT-TIGHTEN-X))
 (20 20 (:TYPE-PRESCRIPTION RTL::ABS-NONNEGATIVE-INTEGERP-TYPE))
 (20 20 (:REWRITE RTL::EXPO-MINUS-ERIC))
 (20 10 (:REWRITE RTL::BITS-WITH-I-NOT-AN-INTEGER))
 (20 2 (:REWRITE RTL::PRODUCT-LESS-THAN-ZERO))
 (18 2 (:REWRITE RTL::A3))
 (12 12 (:REWRITE RTL::BITN-OF-NON-RATIONAL))
 (12 12 (:REWRITE RTL::BITN-MINUS))
 (12 1 (:REWRITE A1))
 (10 10 (:REWRITE RTL::BITS-WITH-X-NOT-RATIONAL))
 (10 10 (:REWRITE RTL::BITS-WITH-J-NOT-AN-INTEGER))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE RTL::BVECP-OF-NON-INTEGER))
 (5 5 (:REWRITE RTL::BITN-OF-EXPT-EQUAL-0))
 (3 3 (:REWRITE RTL::BITN-EQUAL-TO-SILLY-VALUE))
 (3 2 (:REWRITE RTL::EXPO-EXPT2))
 (2 2 (:TYPE-PRESCRIPTION RTL::POWER2P))
 (2 2 (:REWRITE RTL::POWER2P-EXPT2-I))
 (2 2 (:REWRITE RTL::COLLECT-1))
 (1 1 (:REWRITE RTL::COLLECT-CONSTANTS-WITH-DIVISION))
 (1 1 (:REWRITE RTL::BITS-MATCH))
 (1 1 (:REWRITE RTL::BITS-EQUAL-IMPOSSIBLE-CONSTANT))
 (1 1 (:REWRITE RTL::BITS-DROP-SILLY-LOWER-BOUND))
 (1 1 (:REWRITE RTL::BITS-DROP-SILLY-BOUND-4))
 (1 1 (:REWRITE RTL::BITS-DONT-MATCH))
 (1 1 (:REWRITE RTL::BITS-BITS-CONSTANTS))
 (1 1 (:REWRITE RTL::BITN-OF-EXPT-EQUAL-1))
 )
