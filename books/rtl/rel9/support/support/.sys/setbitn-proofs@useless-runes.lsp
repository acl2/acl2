(BVECP)
(BITN)
(SETBITS)
(SETBITN)
(SETBITN-NONNEGATIVE-INTEGER-TYPE)
(SETBITN-NATP)
(SETBITN-BVECP
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE POWER2-INTEGER))
 (1 1 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (1 1 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (1 1 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (1 1 (:REWRITE INTEGERP-MINUS))
 (1 1 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (1 1 (:REWRITE EXPT-COMPARE))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(SETBITN-REWRITE)
(BITN-SETBITN
 (40 4 (:REWRITE BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
 (32 4 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (26 26 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (26 26 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (26 26 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (26 26 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (26 26 (:REWRITE EXPT-COMPARE))
 (26 26 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (22 21 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE DEFAULT-<-2))
 (21 21 (:META CANCEL_PLUS-LESSP-CORRECT))
 (14 1 (:REWRITE BITS-REDUCE))
 (8 8 (:REWRITE POWER2-INTEGER))
 (8 8 (:REWRITE INTEGERP-MINUS))
 (5 5 (:REWRITE DUMB))
 (5 5 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER-2))
 (5 5 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER-2))
 (5 5 (:REWRITE BITS-EXPT-CONSTANT))
 (4 4 (:REWRITE BITS-WITH-X-NOT-RATIONAL))
 (4 4 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER))
 (4 4 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER))
 (3 3 (:REWRITE SETBITN-REWRITE))
 (3 3 (:REWRITE EXPT-COMPARE-EQUAL))
 (3 3 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (3 3 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (3 3 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (3 3 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION A14 . 2))
 (1 1 (:TYPE-PRESCRIPTION A14 . 1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE EXPT-EXECUTE-REWRITE))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE BITS-MATCH))
 (1 1 (:REWRITE BITS-EQUAL-IMPOSSIBLE-CONSTANT))
 (1 1 (:REWRITE BITS-DONT-MATCH))
 )
(SETBITN-SETBITN
 (3217 86 (:REWRITE BITS-SPLIT-AROUND-ZERO))
 (918 585 (:REWRITE DEFAULT-+-2))
 (802 86 (:REWRITE BITS-FORCE-WITH-A-CHOSEN-NEG))
 (689 585 (:REWRITE DEFAULT-+-1))
 (630 463 (:REWRITE DEFAULT-<-1))
 (629 577 (:REWRITE EXPT-COMPARE))
 (577 577 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (577 577 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (577 577 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (564 463 (:REWRITE DEFAULT-<-2))
 (561 561 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (561 561 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (561 73 (:REWRITE CAT-WITH-M-NOT-A-NATURAL))
 (423 345 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (376 2 (:REWRITE BITS-<-1))
 (356 86 (:REWRITE BITS-TAIL))
 (345 345 (:REWRITE EXPT-2-EVALUATOR))
 (287 194 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER-2))
 (218 218 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE))
 (210 10 (:REWRITE CAT-COMPARE-TO-CONSTANT-1))
 (208 194 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER-2))
 (194 194 (:REWRITE BITS-EXPT-CONSTANT))
 (186 155 (:REWRITE BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
 (155 34 (:REWRITE BITS-TAIL-SPECIAL))
 (145 145 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (132 92 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER))
 (114 18 (:REWRITE SETBITS-ALL))
 (103 73 (:REWRITE DEFAULT-*-2))
 (102 92 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER))
 (93 92 (:REWRITE BITS-WITH-X-NOT-RATIONAL))
 (84 73 (:REWRITE CAT-WITH-N-NOT-A-NATURAL))
 (73 73 (:REWRITE DEFAULT-*-1))
 (73 73 (:REWRITE CAT-TIGHTEN-X))
 (48 6 (:REWRITE MOVE-NEGATIVE-CONSTANT-1))
 (38 22 (:REWRITE EXPT-WITH-I-NON-INTEGER-SPECIAL))
 (34 34 (:REWRITE BITS-WITH-BAD-INDEX-2))
 (26 26 (:REWRITE FOLD-CONSTS-IN-+))
 (26 26 (:REWRITE BITS-CAT-CONSTANTS))
 (22 22 (:REWRITE EXPT-COMPARE-EQUAL))
 (22 22 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (16 16 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (16 16 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (16 16 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (12 12 (:REWRITE POWER2-INTEGER))
 (12 12 (:REWRITE INTEGERP-MINUS))
 (12 12 (:REWRITE CAT-BVECP-REWRITE-CONSTANTS))
 (11 11 (:REWRITE CAT-COMBINE-CONSTANTS-GEN))
 (11 11 (:REWRITE CAT-COMBINE-CONSTANTS))
 (8 8 (:TYPE-PRESCRIPTION POWER2P))
 (8 8 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (8 8 (:REWRITE BITS-MATCH))
 (6 6 (:REWRITE BITS-EQUAL-IMPOSSIBLE-CONSTANT))
 (6 6 (:REWRITE BITS-DONT-MATCH))
 (4 4 (:REWRITE POWER2P-EXPT2-I))
 (4 4 (:REWRITE NONNEG-+))
 (4 4 (:REWRITE EXPO-SHIFT-GENERAL))
 (4 4 (:REWRITE EXPO-EXPT2))
 )
(SETBITN-DOES-NOTHING
 (996 10 (:REWRITE BITS-SPLIT-AROUND-ZERO))
 (798 10 (:REWRITE BITS-REDUCE))
 (214 27 (:LINEAR EXPT-WITH-SMALL-N))
 (175 68 (:REWRITE DEFAULT-<-2))
 (174 30 (:TYPE-PRESCRIPTION INTEGERP-PROD))
 (152 95 (:REWRITE DEFAULT-+-2))
 (138 12 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (122 122 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE))
 (121 99 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (113 95 (:REWRITE DEFAULT-+-1))
 (100 10 (:REWRITE BITS-FORCE-WITH-A-CHOSEN-NEG))
 (99 99 (:REWRITE EXPT-EXECUTE-REWRITE))
 (99 99 (:REWRITE EXPT-2-EVALUATOR))
 (84 68 (:REWRITE DEFAULT-<-1))
 (79 79 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (79 79 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (79 79 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (79 79 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (79 79 (:REWRITE EXPT-COMPARE))
 (79 79 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (72 10 (:REWRITE BITS-TAIL))
 (66 10 (:REWRITE A2))
 (63 9 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (46 10 (:REWRITE DEFAULT-*-2))
 (33 3 (:LINEAR BITS-LESS-THAN-X-GEN))
 (33 3 (:LINEAR BITS-LESS-THAN-X))
 (30 12 (:REWRITE BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
 (24 8 (:REWRITE BITS-TAIL-SPECIAL))
 (22 12 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER-2))
 (22 12 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:REWRITE BITS-WITH-X-NOT-RATIONAL))
 (12 12 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER-2))
 (12 12 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER))
 (12 12 (:REWRITE BITS-EXPT-CONSTANT))
 (10 10 (:REWRITE DEFAULT-*-1))
 (10 8 (:REWRITE BITS-WITH-BAD-INDEX-2))
 (3 3 (:REWRITE POWER2-INTEGER))
 (3 3 (:REWRITE INTEGERP-MINUS))
 (2 2 (:REWRITE SETBITN-REWRITE))
 (2 2 (:REWRITE DUMB))
 )
