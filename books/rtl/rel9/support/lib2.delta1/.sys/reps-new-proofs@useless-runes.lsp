(ESGNF_ALT-IS-ESGNF)
(EEXPOF_ALT-IS-ESGNF
 (8 2 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 4 (:REWRITE DEFAULT-+-2))
 (6 4 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE BITS-NEG))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE A4))
 )
(ESIGF_ALT-IS-ESIGF)
(EENCODINGP_ALT)
(EENCODINGP_ALT-IS-EENCODINGP
 (14 10 (:REWRITE DEFAULT-+-2))
 (14 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:REWRITE BVECP-BITN-0))
 (6 2 (:REWRITE BITN-NEG))
 (4 4 (:REWRITE A4))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(EENCODE_ALT
 (6 6 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (6 6 (:TYPE-PRESCRIPTION A14 . 1))
 (2 2 (:TYPE-PRESCRIPTION BIAS-NON-NEGATIVE-INTEGERP-TYPE-PRESCRIPTION))
 )
(EENCODE_ALT-IS-EENCODE
 (943 524 (:REWRITE DEFAULT-+-2))
 (815 524 (:REWRITE DEFAULT-+-1))
 (480 96 (:REWRITE DEFAULT-*-2))
 (317 317 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (264 132 (:REWRITE DEFAULT-<-1))
 (207 207 (:TYPE-PRESCRIPTION EXPO))
 (207 207 (:TYPE-PRESCRIPTION BIAS-NON-NEGATIVE-INTEGERP-TYPE-PRESCRIPTION))
 (192 96 (:REWRITE DEFAULT-*-1))
 (132 132 (:REWRITE DEFAULT-<-2))
 (111 111 (:TYPE-PRESCRIPTION BIAS))
 (96 96 (:TYPE-PRESCRIPTION SIG))
 (96 96 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (96 96 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE))
 (96 96 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE))
 (96 96 (:TYPE-PRESCRIPTION A14 . 1))
 (96 96 (:REWRITE ALREADY-SIG))
 )
(EDECODE_ALT-IS-EDECODE
 (92 16 (:REWRITE DEFAULT-*-2))
 (40 16 (:REWRITE DEFAULT-+-2))
 (30 10 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (24 16 (:REWRITE DEFAULT-+-1))
 (20 16 (:REWRITE DEFAULT-*-1))
 (10 10 (:TYPE-PRESCRIPTION A14 . 1))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE A4))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE A5))
 )
(EENCODINGP_ALT-NOT-ZERO)
(EREPP-EDECODE_ALT)
(EENCODINGP_ALT-EENCODE_ALT)
(EDECODE_ALT-EENCODE_ALT)
(EENCODE_ALT-EDECODE_ALT)
(EXPO-EDECODE_ALT)
(SGN-EDECODE_ALT)
(SIG-EDECODE_ALT)
(REBIAS-DOWN_ALT)
(BITN-LOGNOT-G
 (58 45 (:REWRITE DEFAULT-*-2))
 (51 45 (:REWRITE DEFAULT-*-1))
 (32 20 (:REWRITE DEFAULT-+-2))
 (32 2 (:LINEAR FL-DEF-LINEAR-PART-2))
 (30 2 (:LINEAR FL-NON-NEGATIVE-LINEAR))
 (28 20 (:REWRITE DEFAULT-+-1))
 (26 2 (:LINEAR FL-DEF-LINEAR-PART-1))
 (23 4 (:REWRITE FL-OF-ODD/2))
 (20 2 (:REWRITE PRODUCT-LESS-THAN-ZERO))
 (13 7 (:REWRITE EVEN-MEANS-HALF-IS-INTEGER))
 (11 3 (:REWRITE FL-OF-NON-RATIONAL))
 (10 10 (:REWRITE POWER2-INTEGER))
 (10 10 (:REWRITE INTEGERP-MINUS))
 (10 1 (:REWRITE MOD-DOES-NOTHING))
 (9 2 (:REWRITE A10))
 (7 7 (:REWRITE INTEGERP-PROD))
 (6 6 (:TYPE-PRESCRIPTION EVEN))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE COLLECT-CONSTANTS-IN-EQUAL-OF-SUMS))
 (6 2 (:REWRITE RATIONALP-PROD))
 (6 2 (:REWRITE BVECP-BITN-0))
 (6 2 (:REWRITE BITN-BVECP-1))
 (6 2 (:LINEAR EXPT-2-TYPE-LINEAR))
 (5 5 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (5 5 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (5 5 (:REWRITE EXPT-COMPARE))
 (5 5 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (4 4 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 (4 4 (:LINEAR FL-MONOTONE-LINEAR))
 (4 4 (:LINEAR EXPT-EXCEEDS-2))
 (3 3 (:REWRITE MOVE-NEGATIVE-CONSTANT-1))
 (3 3 (:REWRITE MOD-WHEN-Y-IS-AN-INVERSE))
 (3 3 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (3 3 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (3 3 (:REWRITE EXPT-COMPARE-EQUAL))
 (3 3 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (3 3 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (3 3 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 1 (:REWRITE INTEGERP-IMPLIES-NOT-COMPLEX-RATIONALP))
 (3 1 (:REWRITE A4))
 (2 2 (:REWRITE BITN-NEG))
 (2 2 (:LINEAR N<=FL-LINEAR))
 (2 2 (:LINEAR EXPT-WITH-SMALL-N))
 (1 1 (:REWRITE MOD-WITH-X-A-NON-ACL2-NUMBER-IS-ZERO))
 )
(REBIAS-UP_ALT
 (316 256 (:REWRITE DEFAULT-*-2))
 (304 256 (:REWRITE DEFAULT-*-1))
 (133 7 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (133 7 (:REWRITE BITS-NEG))
 (129 83 (:REWRITE DEFAULT-+-2))
 (89 83 (:REWRITE DEFAULT-+-1))
 (51 19 (:REWRITE BVECP-BITN-0))
 (48 48 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (48 48 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (48 48 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (48 48 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (48 48 (:REWRITE EXPT-COMPARE))
 (48 48 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (42 7 (:REWRITE BITS-TAIL))
 (36 19 (:REWRITE BITN-NEG))
 (33 33 (:REWRITE DEFAULT-<-2))
 (33 33 (:REWRITE DEFAULT-<-1))
 (33 33 (:META CANCEL_PLUS-LESSP-CORRECT))
 (33 19 (:REWRITE A4))
 (30 30 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (30 30 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (30 26 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (26 26 (:REWRITE EXPT-2-EVALUATOR))
 (13 13 (:REWRITE EXPT-COMPARE-EQUAL))
 (13 13 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (13 13 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (13 13 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (13 13 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (9 9 (:LINEAR EXPT-WITH-SMALL-N))
 (8 8 (:REWRITE POWER2-INTEGER))
 (8 8 (:REWRITE INTEGERP-MINUS))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE BITN-BVECP-1))
 (3 3 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (2 2 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (2 2 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE))
 (2 2 (:TYPE-PRESCRIPTION A14 . 1))
 (1 1 (:REWRITE NONNEG-+))
 )
(ISGNF_ALT-IS-ISGNF)
(IEXPOF_ALT-IS-IEXPOF
 (76 2 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (50 4 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS-2))
 (50 2 (:REWRITE BITS-NEG))
 (32 32 (:TYPE-PRESCRIPTION NONNEG-+-TYPE))
 (32 8 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (24 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (14 8 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (10 10 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (10 10 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (10 10 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (10 10 (:REWRITE EXPT-COMPARE))
 (10 10 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (10 8 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE A4))
 )
(ISIGF_ALT-IS-ISIGF)
(NENCODINGP_ALT-IS-NENCODING
 (152 4 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (100 8 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS-2))
 (100 4 (:REWRITE BITS-NEG))
 (74 66 (:TYPE-PRESCRIPTION NONNEG-+-TYPE))
 (66 18 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (52 16 (:META CANCEL_PLUS-LESSP-CORRECT))
 (42 20 (:REWRITE DEFAULT-+-2))
 (26 20 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (24 24 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (24 24 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (24 24 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (24 24 (:REWRITE EXPT-COMPARE))
 (24 24 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (24 12 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 12 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (4 4 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (4 4 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE))
 (4 4 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE))
 (4 4 (:TYPE-PRESCRIPTION A14 . 1))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE A4))
 (2 2 (:REWRITE POWER2-INTEGER))
 (2 2 (:REWRITE INTEGERP-MINUS))
 (2 2 (:REWRITE EXPT-EXECUTE-REWRITE))
 (2 2 (:REWRITE EXPT-2-EVALUATOR))
 )
(DENCODINGP_ALT-IS-DENCODING
 (116 4 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (88 4 (:REWRITE BITS-NEG))
 (74 12 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (50 4 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS-2))
 (40 40 (:TYPE-PRESCRIPTION NONNEG-+-TYPE))
 (28 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (24 14 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (18 18 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (18 18 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (18 18 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (18 18 (:REWRITE EXPT-COMPARE))
 (18 18 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (18 14 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 8 (:REWRITE DEFAULT-<-1))
 (12 2 (:REWRITE BITS-TAIL))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE A4))
 (4 4 (:REWRITE EXPT-COMPARE-EQUAL))
 (4 4 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (4 4 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (4 4 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (4 4 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (4 4 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(IENCODINGP_ALT)
(IENCODINGP_ALT-IS-IENCODING)
(NOT-BOTH-NENCODINGP_ALT-AND-DENCODINGP_ALT)
(NENCODE_ALT-IS-NENCODE
 (2136 860 (:REWRITE DEFAULT-+-1))
 (2120 860 (:REWRITE DEFAULT-+-2))
 (1564 152 (:TYPE-PRESCRIPTION INTEGERP-PROD))
 (1292 76 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (1076 176 (:REWRITE DEFAULT-*-2))
 (736 368 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE))
 (688 368 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (415 415 (:REWRITE POWER2-INTEGER))
 (368 368 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE))
 (368 368 (:TYPE-PRESCRIPTION A14 . 1))
 (365 365 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (320 112 (:REWRITE INTEGERP-+))
 (315 315 (:REWRITE INTEGERP-MINUS))
 (264 176 (:REWRITE DEFAULT-*-1))
 (216 114 (:REWRITE DEFAULT-<-1))
 (190 190 (:TYPE-PRESCRIPTION EXPO-OF-INTEGER-TYPE))
 (190 190 (:TYPE-PRESCRIPTION EXPO-INTEGER-TYPE))
 (190 190 (:TYPE-PRESCRIPTION BIAS-NON-NEGATIVE-INTEGERP-TYPE-PRESCRIPTION))
 (154 154 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (154 154 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (154 154 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (154 154 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (154 154 (:REWRITE EXPT-COMPARE))
 (154 154 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (129 129 (:TYPE-PRESCRIPTION BIAS))
 (128 112 (:REWRITE INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (114 114 (:REWRITE DEFAULT-<-2))
 (114 114 (:META CANCEL_PLUS-LESSP-CORRECT))
 (106 90 (:REWRITE EVEN-ODD-5))
 (102 102 (:REWRITE EXPO-SHIFT-GENERAL))
 (102 102 (:REWRITE EXPO-OF-NOT-RATIONALP))
 (102 102 (:REWRITE EXPO-MINUS-ERIC))
 (88 88 (:REWRITE ALREADY-SIG))
 (76 76 (:REWRITE EXPT-EXECUTE-REWRITE))
 (76 76 (:REWRITE EXPT-2-EVALUATOR))
 (76 76 (:REWRITE A3))
 (50 24 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER))
 (44 44 (:REWRITE EXPT-COMPARE-EQUAL))
 (44 44 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (44 44 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (44 44 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (44 44 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (44 44 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (44 44 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (40 40 (:REWRITE NONNEG-+))
 (32 32 (:REWRITE A4))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE RATIONALP-SUM-WHEN-ONE-ARG-IS-RATIONAL))
 (8 8 (:REWRITE RATIONALP-SUM))
 (4 4 (:REWRITE RATIONALP-+))
 )
(DENCODE_ALT-IS-DENCODE
 (70393 468 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (26142 936 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER-3))
 (26056 2532 (:REWRITE INTEGERP-+))
 (16241 4792 (:REWRITE DEFAULT-+-2))
 (14563 14563 (:TYPE-PRESCRIPTION BIAS-NON-NEGATIVE-INTEGERP-TYPE-PRESCRIPTION))
 (12815 2532 (:REWRITE INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (11026 11026 (:TYPE-PRESCRIPTION BIAS))
 (11006 468 (:REWRITE DEFAULT-*-2))
 (9497 9497 (:TYPE-PRESCRIPTION EXPO-OF-INTEGER-TYPE))
 (9497 9497 (:TYPE-PRESCRIPTION EXPO-INTEGER-TYPE))
 (6845 4792 (:REWRITE DEFAULT-+-1))
 (6370 1702 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER))
 (5995 468 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (4909 500 (:REWRITE RATIONALP-SUM))
 (4655 4655 (:REWRITE POWER2-INTEGER))
 (3607 468 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-INTEGER-TYPE))
 (2837 2837 (:REWRITE INTEGERP-MINUS))
 (1960 1960 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1738 936 (:REWRITE INTEGERP-IMPLIES-NOT-COMPLEX-RATIONALP))
 (1552 1552 (:REWRITE A4))
 (1494 1494 (:REWRITE FOLD-CONSTS-IN-+))
 (943 514 (:REWRITE DEFAULT-<-1))
 (936 468 (:REWRITE DEFAULT-*-1))
 (688 688 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (688 688 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (688 688 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (688 688 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (688 688 (:REWRITE EXPT-COMPARE))
 (688 688 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (514 514 (:REWRITE DEFAULT-<-2))
 (514 514 (:META CANCEL_PLUS-LESSP-CORRECT))
 (468 468 (:TYPE-PRESCRIPTION SIG))
 (468 468 (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE))
 (468 468 (:TYPE-PRESCRIPTION A14 . 1))
 (468 468 (:REWRITE EXPT-EXECUTE-REWRITE))
 (468 468 (:REWRITE EXPT-2-EVALUATOR))
 (468 468 (:REWRITE EXPO-SHIFT-GENERAL))
 (468 468 (:REWRITE EXPO-OF-NOT-RATIONALP))
 (468 468 (:REWRITE EXPO-MINUS-ERIC))
 (468 468 (:REWRITE ALREADY-SIG))
 (214 174 (:REWRITE NONNEG-+))
 (196 196 (:REWRITE EXPT-COMPARE-EQUAL))
 (196 196 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (196 196 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (196 196 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (196 196 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (196 196 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (196 196 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (148 84 (:REWRITE EVEN-ODD-5))
 (32 32 (:REWRITE RATIONALP-SUM-WHEN-ONE-ARG-IS-RATIONAL))
 (16 16 (:REWRITE RATIONALP-+))
 )
(IENCODE_ALT)
(IENCODE_ALT-IS-IENCODE)
(NDECODE_ALT-IS-NDECODE
 (836 8 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (812 96 (:REWRITE DEFAULT-+-2))
 (586 54 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (392 40 (:REWRITE DEFAULT-*-2))
 (384 12 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (304 8 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER-3))
 (288 20 (:REWRITE INTEGERP-+))
 (276 20 (:REWRITE INTEGERP-+-REDUCE-LEADING-CONSTANT))
 (276 12 (:REWRITE BITS-NEG))
 (240 44 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (236 96 (:REWRITE DEFAULT-+-1))
 (200 16 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS-2))
 (192 20 (:REWRITE INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (168 40 (:REWRITE INTEGERP-MINUS))
 (144 8 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER))
 (120 4 (:REWRITE RATIONALP-SUM))
 (106 34 (:META CANCEL_PLUS-LESSP-CORRECT))
 (100 20 (:REWRITE A5))
 (84 12 (:REWRITE INTEGERP-IMPLIES-NOT-COMPLEX-RATIONALP))
 (60 60 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (60 60 (:REWRITE POWER2-INTEGER))
 (60 60 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (60 60 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (60 60 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (60 60 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (60 60 (:REWRITE EXPT-COMPARE))
 (60 60 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (54 54 (:TYPE-PRESCRIPTION A14 . 1))
 (50 2 (:REWRITE BITN-NEG))
 (48 26 (:REWRITE DEFAULT-<-1))
 (44 40 (:REWRITE DEFAULT-*-1))
 (38 30 (:REWRITE A4))
 (32 4 (:REWRITE UNICITY-OF-0))
 (26 26 (:REWRITE DEFAULT-<-2))
 (24 16 (:REWRITE INTEGERP-PROD))
 (24 4 (:REWRITE BITS-TAIL))
 (22 22 (:REWRITE FOLD-CONSTS-IN-+))
 (20 8 (:REWRITE COMPLEX-RATIONALP-PROD))
 (12 12 (:TYPE-PRESCRIPTION BVECP))
 (8 8 (:REWRITE EXPT-EXECUTE-REWRITE))
 (8 8 (:REWRITE EXPT-2-EVALUATOR))
 (8 4 (:DEFINITION NOT))
 (6 2 (:REWRITE BVECP-BITN-0))
 (2 2 (:REWRITE EXPT-COMPARE-EQUAL))
 (2 2 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (2 2 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (2 2 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(DDECODE_ALT-IS-DECODE
 (568 4 (:REWRITE EXPT-WITH-I-NON-INTEGER))
 (276 32 (:REWRITE DEFAULT-*-2))
 (188 12 (:REWRITE INTEGERP-+))
 (176 16 (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE))
 (168 40 (:REWRITE INTEGERP-MINUS))
 (168 12 (:REWRITE INTEGERP-+-REDUCE-LEADING-CONSTANT))
 (160 12 (:REWRITE INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT))
 (144 8 (:REWRITE INTEGERP-SUM-TAKE-OUT-KNOWN-INTEGER))
 (112 12 (:REWRITE COLLECT-CONSTANTS-IN-<-OF-SUMS))
 (112 4 (:REWRITE RATIONALP-SUM))
 (100 20 (:REWRITE A5))
 (84 12 (:REWRITE INTEGERP-IMPLIES-NOT-COMPLEX-RATIONALP))
 (80 28 (:REWRITE DEFAULT-+-2))
 (80 4 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (76 4 (:REWRITE BITS-NEG))
 (52 52 (:REWRITE POWER2-INTEGER))
 (50 2 (:REWRITE BITN-NEG))
 (42 28 (:REWRITE DEFAULT-+-1))
 (36 32 (:REWRITE DEFAULT-*-1))
 (32 32 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 16 (:REWRITE INTEGERP-PROD))
 (24 4 (:REWRITE UNICITY-OF-0))
 (24 4 (:REWRITE BITS-TAIL))
 (22 14 (:REWRITE A4))
 (20 20 (:REWRITE NON-INTEGERP-<-INTEGERP))
 (20 20 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (20 20 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (20 20 (:REWRITE INTEGERP-<-NON-INTEGERP))
 (20 20 (:REWRITE EXPT-COMPARE))
 (20 20 (:REWRITE CANCEL-COMMON-FACTORS-IN-<))
 (20 8 (:REWRITE COMPLEX-RATIONALP-PROD))
 (16 16 (:TYPE-PRESCRIPTION A14 . 1))
 (16 10 (:REWRITE DEFAULT-<-1))
 (12 12 (:TYPE-PRESCRIPTION BVECP))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 4 (:DEFINITION NOT))
 (6 2 (:REWRITE BVECP-BITN-0))
 (4 4 (:REWRITE EXPT-EXECUTE-REWRITE))
 (4 4 (:REWRITE EXPT-2-EVALUATOR))
 (2 2 (:REWRITE EXPT-COMPARE-EQUAL))
 (2 2 (:REWRITE EQUAL-OF-PREDS-REWRITE))
 (2 2 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL-WITH-0))
 (2 2 (:REWRITE CANCEL-COMMON-FACTORS-IN-EQUAL))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(IDECODE_ALT)
(IDECODE_ALT-IS-IDECODE)
(SGN-IDECODE_ALT)
(EXPO-IDECODE_ALT)
(SIG-IDECODE_ALT)
(IENCODINGP_ALT-IENCODE_ALT)
(IREPP-IDECODE_ALT)
(IDECODE_ALT-IENCODE_ALT)
(IENCODE_ALT-IDECODE_ALT)
