(X86ISA::FORMAL-FORCE-LIST)
(X86ISA::LOGEXT-WHEN-UNSIGNED-BYTE-P-AND-SIGN-CHANGES
 (10913 160 (:REWRITE NATP-WHEN-INTEGERP))
 (10845 82
        (:REWRITE BITOPS::LOGBITP-TO-LOWER-BOUND))
 (8306
  8306
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8306
      8306
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8306
     8306
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8306 8306
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8009 70
       (:REWRITE BITOPS::BOUNDS-TO-LOGBITP-LEMMA))
 (7325 1052
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4626 19 (:REWRITE CANCEL-MOD-+))
 (4479 1835 (:REWRITE DEFAULT-PLUS-2))
 (4476 128 (:REWRITE NFIX-WHEN-NOT-NATP))
 (4304 749
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (4146 66 (:LINEAR EXPT-<=-1-TWO))
 (4101 575 (:REWRITE DEFAULT-TIMES-2))
 (3907 35 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (3599 160 (:REWRITE NATP-WHEN-GTE-0))
 (3302 1525 (:REWRITE DEFAULT-LESS-THAN-2))
 (2968 19 (:REWRITE MOD-X-Y-=-X . 3))
 (2759 575 (:REWRITE DEFAULT-TIMES-1))
 (2744 1823 (:REWRITE DEFAULT-PLUS-1))
 (2561 66 (:LINEAR EXPT-X->=-X))
 (2561 66 (:LINEAR EXPT-X->-X))
 (2453 1516 (:REWRITE DEFAULT-LESS-THAN-1))
 (2406 19 (:REWRITE MOD-ZERO . 3))
 (1949 66 (:LINEAR EXPT-<-1-TWO))
 (1798 19 (:REWRITE |(integerp (- x))|))
 (1628 438 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1628 438 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1586 438
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1586 438
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1525 1525 (:REWRITE THE-FLOOR-BELOW))
 (1525 1525 (:REWRITE THE-FLOOR-ABOVE))
 (1509 36 (:REWRITE ZP-WHEN-INTEGERP))
 (1498 1498
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1498 1498
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1470 36 (:REWRITE ZP-WHEN-GT-0))
 (1444 23 (:REWRITE DEFAULT-MOD-RATIO))
 (1357 1064
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1260 1260
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1258 1258
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1258 1258
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1258 1258
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1115 1067
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1110 1064 (:REWRITE |(< c (- x))|))
 (1089 1067 (:REWRITE |(< (- x) (- y))|))
 (1087 187 (:REWRITE DEFAULT-MINUS))
 (1086 1064 (:REWRITE |(< (- x) c)|))
 (1071 1067 (:REWRITE |(< (/ x) (/ y))|))
 (1067 1067
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1067 1067
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1067 1067
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1067 1067
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1067 1067
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1067 1067
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1067 1067
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1064 1064 (:REWRITE INTEGERP-<-CONSTANT))
 (1064 1064 (:REWRITE CONSTANT-<-INTEGERP))
 (1022 82
       (:REWRITE BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (970 744
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (886 25 (:REWRITE |(* (- x) y)|))
 (850 66
      (:LINEAR BITOPS::LOGBITP-TO-LOWER-BOUND))
 (850 66
      (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (780 6 (:LINEAR MOD-BOUNDS-3))
 (767 72 (:REWRITE DEFAULT-DIVIDE))
 (749 749
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (730 96 (:REWRITE |(< 0 (/ x))|))
 (726 19 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (726 19
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (723 169 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (634 23 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (598 372 (:REWRITE DEFAULT-EXPT-2))
 (536 19 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (536 19 (:REWRITE MOD-X-Y-=-X . 2))
 (534 19 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (522 70
      (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (480 19 (:REWRITE MOD-X-Y-=-X . 4))
 (438 438 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (438 438
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (438 438
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (438 438
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (436 52 (:REWRITE ACL2-NUMBERP-X))
 (390 19 (:REWRITE MOD-ZERO . 4))
 (372 372 (:REWRITE DEFAULT-EXPT-1))
 (372 372 (:REWRITE |(expt 1/c n)|))
 (372 372 (:REWRITE |(expt (- x) n)|))
 (350 350 (:REWRITE |(< (+ c/d x) y)|))
 (344 19
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (344 19 (:REWRITE MOD-CANCEL-*-CONST))
 (344 19
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (344 19
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (343 343 (:REWRITE |(< (* x y) 0)|))
 (336 12 (:LINEAR MOD-BOUNDS-2))
 (291 291
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (274 274 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (249 23 (:REWRITE DEFAULT-MOD-2))
 (221 221 (:REWRITE |(< x (+ c/d y))|))
 (218 218 (:REWRITE |(< 0 (* x y))|))
 (210 8 (:REWRITE |(< x (if a b c))|))
 (209 19
      (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (192 48 (:REWRITE RATIONALP-X))
 (163 10
      (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (132 132
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (132 132
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (132 132
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (125 125 (:REWRITE INTEGERP-MINUS-X))
 (124 124 (:META META-INTEGERP-CORRECT))
 (106 4 (:REWRITE |(< (if a b c) x)|))
 (96 18 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (78 78 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (78 78
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (78 78
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (75 75 (:REWRITE |(< (+ (- c) x) y)|))
 (73 73
     (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (70 70
     (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (69 68 (:REWRITE |(< (/ x) 0)|))
 (67 67 (:LINEAR EXPT-LINEAR-LOWER-<))
 (66 66 (:REWRITE |(< y (+ (- c) x))|))
 (66 66 (:LINEAR EXPT-LINEAR-UPPER-<))
 (66 66 (:LINEAR EXPT->=-1-TWO))
 (66 66 (:LINEAR EXPT->-1-TWO))
 (66 66 (:LINEAR EXPT-<=-1-ONE))
 (66 66 (:LINEAR EXPT-<-1-ONE))
 (66 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (59 3 (:REWRITE BITOPS::LOGCDR->-CONST))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (48 48 (:REWRITE REDUCE-RATIONALP-+))
 (48 48 (:REWRITE REDUCE-RATIONALP-*))
 (48 48 (:REWRITE RATIONALP-MINUS-X))
 (48 48 (:META META-RATIONALP-CORRECT))
 (45 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (45 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (45 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (38 24 (:REWRITE |(equal (/ x) c)|))
 (34 24 (:REWRITE |(equal (- x) (- y))|))
 (29 24 (:REWRITE |(equal (/ x) (/ y))|))
 (25 23 (:REWRITE DEFAULT-MOD-1))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (24 24
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (24 24 (:REWRITE |(equal c (/ x))|))
 (24 4 (:REWRITE |(- (+ x y))|))
 (24 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (24 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (24 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (23 23
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (23 23 (:REWRITE |(equal c (- x))|))
 (23 23 (:REWRITE |(equal (- x) c)|))
 (22 22 (:TYPE-PRESCRIPTION BITP))
 (20 20
     (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (19 19
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (19 19 (:REWRITE |(mod x (- y))| . 3))
 (19 19 (:REWRITE |(mod x (- y))| . 2))
 (19 19 (:REWRITE |(mod x (- y))| . 1))
 (19 19
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (19 19 (:REWRITE |(mod (- x) y)| . 3))
 (19 19 (:REWRITE |(mod (- x) y)| . 2))
 (19 19 (:REWRITE |(mod (- x) y)| . 1))
 (19 19
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (19 19 (:REWRITE |(- (* c x))|))
 (16 16 (:REWRITE |(equal (+ (- c) x) y)|))
 (12 12 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (7 7
    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE |(equal (expt 2 n) c)|))
 (6 6 (:REWRITE BITOPS::LOGCDR-<-CONST))
 (5 3 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (5 3 (:REWRITE |(- (- x))|))
 (2 2 (:REWRITE |(equal x (if a b c))|))
 (2 2 (:REWRITE |(equal (if a b c) x)|))
 (2 2 (:REWRITE |(+ x (if a b c))|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(X86ISA::LEMMA (49 49
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
               (8 1 (:REWRITE NATP-POSP))
               (7 1
                  (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
               (6 1 (:LINEAR EXPT->-1))
               (5 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
               (5 4 (:REWRITE DEFAULT-<-1))
               (4 4 (:REWRITE DEFAULT-<-2))
               (3 1 (:REWRITE ZP-WHEN-GT-0))
               (3 1 (:REWRITE NATP-WHEN-GTE-0))
               (3 1 (:REWRITE <-0-+-NEGATIVE-1))
               (2 2 (:TYPE-PRESCRIPTION NATP))
               (2 2
                  (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
               (1 1 (:REWRITE ZP-WHEN-INTEGERP))
               (1 1 (:REWRITE ZP-OPEN))
               (1 1 (:REWRITE POSP-RW))
               (1 1 (:REWRITE NATP-WHEN-INTEGERP))
               (1 1 (:REWRITE NATP-RW))
               (1 1
                  (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
               (1 1
                  (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE<1))
               (1 1
                  (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
               (1 1 (:REWRITE EXPONENTS-ADD))
               (1 1 (:REWRITE DEFAULT-+-2))
               (1 1 (:REWRITE DEFAULT-+-1))
               (1 1
                  (:LINEAR BITOPS::LOGBITP-TO-LOWER-BOUND))
               (1 1
                  (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP)))
(X86ISA::LOGHEAD-WHEN-SIGNED-BYTE-P-AND-SIGN-CHANGES
 (1324 168 (:REWRITE DEFAULT-LESS-THAN-2))
 (918 5 (:REWRITE CANCEL-MOD-+))
 (825 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (789 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (769 143 (:REWRITE DEFAULT-LESS-THAN-1))
 (758 86 (:REWRITE ACL2-NUMBERP-X))
 (603 125
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (575 26
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (527 5
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (519 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (471 5
      (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (468 16 (:LINEAR EXPT-X->-X))
 (459 16 (:LINEAR EXPT-X->=-X))
 (453 4 (:DEFINITION ZEROP))
 (435 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (428 16 (:LINEAR EXPT-<=-1-TWO))
 (386 16 (:LINEAR EXPT-<-1-TWO))
 (361 5 (:REWRITE MOD-X-Y-=-X . 4))
 (360
  360
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (360 360
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (360
     360
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (360 360
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (360 360
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (336 84 (:REWRITE RATIONALP-X))
 (297 51 (:REWRITE DEFAULT-PLUS-2))
 (269 269
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (269 269
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (269 269
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (259 3 (:REWRITE |(+ y (+ x z))|))
 (244 5 (:REWRITE MOD-ZERO . 3))
 (237 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (237 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (224 24 (:REWRITE IFIX-EQUAL-TO-0))
 (222 5 (:REWRITE MOD-X-Y-=-X . 2))
 (220 114
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (216 114
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (212 4 (:LINEAR MOD-BOUNDS-2))
 (196 5 (:REWRITE MOD-X-Y-=-X . 3))
 (185 11 (:REWRITE NORMALIZE-ADDENDS))
 (185 5 (:REWRITE |(integerp (- x))|))
 (183 114 (:REWRITE SIMPLIFY-SUMS-<))
 (177 35 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (177 35 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (177 35
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (177 35
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (168 168 (:REWRITE THE-FLOOR-BELOW))
 (168 168 (:REWRITE THE-FLOOR-ABOVE))
 (159 12 (:REWRITE |(+ c (+ d x))|))
 (140 20 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
 (136 5 (:REWRITE MOD-ZERO . 4))
 (130 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (125 125
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (125 125
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (122 5 (:REWRITE DEFAULT-MOD-RATIO))
 (114 114
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (114 114 (:REWRITE INTEGERP-<-CONSTANT))
 (114 114 (:REWRITE CONSTANT-<-INTEGERP))
 (114 114
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (114 114
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (114 114
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (114 114
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (114 114 (:REWRITE |(< c (- x))|))
 (114 114
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (114 114
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (114 114
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (114 114
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (114 114 (:REWRITE |(< (/ x) (/ y))|))
 (114 114 (:REWRITE |(< (- x) c)|))
 (114 114 (:REWRITE |(< (- x) (- y))|))
 (112 45 (:REWRITE DEFAULT-PLUS-1))
 (105 4 (:REWRITE |(< x (if a b c))|))
 (102 5 (:REWRITE |(* (- x) y)|))
 (99 99 (:REWRITE REDUCE-INTEGERP-+))
 (99 99 (:REWRITE INTEGERP-MINUS-X))
 (99 99 (:META META-INTEGERP-CORRECT))
 (97 25 (:REWRITE DEFAULT-TIMES-2))
 (94 17 (:REWRITE DEFAULT-MINUS))
 (84 84 (:REWRITE REDUCE-RATIONALP-+))
 (84 84 (:REWRITE REDUCE-RATIONALP-*))
 (84 84 (:REWRITE RATIONALP-MINUS-X))
 (84 84 (:META META-RATIONALP-CORRECT))
 (84 3
     (:REWRITE BITOPS::LOGBITP-TO-LOWER-BOUND))
 (82 3
     (:REWRITE BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (80 8
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (80 8
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (73 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (73 3 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (70 4
     (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (68 1 (:REWRITE |(+ x x)|))
 (65 26
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (62 2 (:LINEAR MOD-BOUNDS-3))
 (58 17 (:REWRITE DEFAULT-DIVIDE))
 (53 2 (:REWRITE |(< (if a b c) x)|))
 (48 48 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (46 1 (:REWRITE POSP-REDEFINITION))
 (44 44 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (44 25 (:REWRITE DEFAULT-TIMES-1))
 (44 5
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (44 5 (:REWRITE MOD-CANCEL-*-CONST))
 (44 5
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (44 5
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (44 3 (:REWRITE ODD-EXPT-THM))
 (43 7 (:DEFINITION FIX))
 (40 40 (:REWRITE |(< (* x y) 0)|))
 (40 4
     (:REWRITE BITOPS::BOUNDS-TO-LOGBITP-LEMMA))
 (40 4 (:REWRITE BITOPS::BOUNDS-TO-LOGBITP))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (38 38 (:REWRITE |(< (/ x) 0)|))
 (37 37 (:REWRITE |(< 0 (* x y))|))
 (36 2 (:REWRITE ZP-WHEN-GT-0))
 (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (35 35
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (35 35 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (35 35
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (35 26 (:REWRITE |(equal (- x) (- y))|))
 (34 34 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (33 1 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< 0 (/ x))|))
 (32 32
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (32 32
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (32 1 (:REWRITE |(* c (expt d n))|))
 (26 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (26 26 (:REWRITE |(equal c (/ x))|))
 (26 26 (:REWRITE |(equal c (- x))|))
 (26 26 (:REWRITE |(equal (/ x) c)|))
 (26 26 (:REWRITE |(equal (/ x) (/ y))|))
 (26 26 (:REWRITE |(equal (- x) c)|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (24 24
     (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
 (24 24 (:REWRITE IFIX-EQUAL-TO-NONZERO))
 (24 24 (:REWRITE DEFAULT-EXPT-2))
 (24 24 (:REWRITE DEFAULT-EXPT-1))
 (24 24 (:REWRITE |(expt 1/c n)|))
 (24 24 (:REWRITE |(expt (- x) n)|))
 (24 3 (:REWRITE |(/ (expt x n))|))
 (23 23
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (23 23
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (23 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (23 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (22 13 (:REWRITE |(+ 0 x)|))
 (18 5 (:REWRITE DEFAULT-MOD-2))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (16 16 (:LINEAR EXPT->=-1-TWO))
 (16 16 (:LINEAR EXPT->-1-TWO))
 (16 16 (:LINEAR EXPT-<=-1-ONE))
 (16 16 (:LINEAR EXPT-<-1-ONE))
 (15 15
     (:LINEAR BITOPS::LOGBITP-TO-LOWER-BOUND))
 (15 15
     (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 5 (:REWRITE DEFAULT-MOD-1))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:TYPE-PRESCRIPTION LOGBITP))
 (5 5
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5 (:REWRITE |(mod x (- y))| . 3))
 (5 5 (:REWRITE |(mod x (- y))| . 2))
 (5 5 (:REWRITE |(mod x (- y))| . 1))
 (5 5
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(mod (- x) y)| . 3))
 (5 5 (:REWRITE |(mod (- x) y)| . 2))
 (5 5 (:REWRITE |(mod (- x) y)| . 1))
 (5 5
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(- (* c x))|))
 (5 2 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (4 4
    (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (3 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 (3 3 (:REWRITE |(+ x (- x))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1
    (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (1 1 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (1 1 (:REWRITE |(* 1 x)|)))
(X86ISA::NP-DEF-N)
(X86ISA::NP-DEFS)
(X86ISA::N01P$INLINE)
(X86ISA::N01$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I01P$INLINE)
(X86ISA::I01$INLINE)
(X86ISA::N01-TO-I01$INLINE
     (67 7
         (:REWRITE X86ISA::LOGEXT-WHEN-UNSIGNED-BYTE-P-AND-SIGN-CHANGES))
     (24 3 (:REWRITE LOGEXT-IDENTITY))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (12 3
         (:REWRITE BITOPS::LOGEXT-OF-1-I-WHEN-LOGCAR-1))
     (12 3
         (:REWRITE BITOPS::LOGEXT-OF-1-I-WHEN-LOGCAR-0))
     (12 3 (:DEFINITION SIGNED-BYTE-P))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (9 9 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-+-1))
     (7 7
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (7 7
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (6 6 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (6 6
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (6 6 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (6 6 (:DEFINITION BIT->BOOL$INLINE))
     (3 3 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (3 3
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (3 3
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I01-TO-N01$INLINE
     (18 2
         (:REWRITE X86ISA::LOGHEAD-WHEN-SIGNED-BYTE-P-AND-SIGN-CHANGES))
     (7 1 (:REWRITE LOGHEAD-IDENTITY))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 1 (:DEFINITION UNSIGNED-BYTE-P))
     (3 3
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (3 3 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (3 3 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-+-1))
     (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (1 1
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N02P$INLINE)
(X86ISA::N02$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I02P$INLINE)
(X86ISA::I02$INLINE)
(X86ISA::N02-TO-I02$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I02-TO-N02$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (12 12 (:REWRITE DEFAULT-<-2))
                           (12 12 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N03P$INLINE)
(X86ISA::N03$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I03P$INLINE)
(X86ISA::I03$INLINE)
(X86ISA::N03-TO-I03$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I03-TO-N03$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N04P$INLINE)
(X86ISA::N04$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I04P$INLINE)
(X86ISA::I04$INLINE)
(X86ISA::N04-TO-I04$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I04-TO-N04$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N05P$INLINE)
(X86ISA::N05$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I05P$INLINE)
(X86ISA::I05$INLINE)
(X86ISA::N05-TO-I05$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I05-TO-N05$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N06P$INLINE)
(X86ISA::N06$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I06P$INLINE)
(X86ISA::I06$INLINE)
(X86ISA::N06-TO-I06$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I06-TO-N06$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N08P$INLINE)
(X86ISA::N08$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I08P$INLINE)
(X86ISA::I08$INLINE)
(X86ISA::N08-TO-I08$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I08-TO-N08$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N09P$INLINE)
(X86ISA::N09$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I09P$INLINE)
(X86ISA::I09$INLINE)
(X86ISA::N09-TO-I09$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I09-TO-N09$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N11P$INLINE)
(X86ISA::N11$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I11P$INLINE)
(X86ISA::I11$INLINE)
(X86ISA::N11-TO-I11$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I11-TO-N11$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N12P$INLINE)
(X86ISA::N12$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I12P$INLINE)
(X86ISA::I12$INLINE)
(X86ISA::N12-TO-I12$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I12-TO-N12$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N16P$INLINE)
(X86ISA::N16$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I16P$INLINE)
(X86ISA::I16$INLINE)
(X86ISA::N16-TO-I16$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I16-TO-N16$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N17P$INLINE)
(X86ISA::N17$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I17P$INLINE)
(X86ISA::I17$INLINE)
(X86ISA::N17-TO-I17$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I17-TO-N17$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N18P$INLINE)
(X86ISA::N18$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I18P$INLINE)
(X86ISA::I18$INLINE)
(X86ISA::N18-TO-I18$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I18-TO-N18$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N20P$INLINE)
(X86ISA::N20$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I20P$INLINE)
(X86ISA::I20$INLINE)
(X86ISA::N20-TO-I20$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I20-TO-N20$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N21P$INLINE)
(X86ISA::N21$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I21P$INLINE)
(X86ISA::I21$INLINE)
(X86ISA::N21-TO-I21$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I21-TO-N21$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N22P$INLINE)
(X86ISA::N22$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I22P$INLINE)
(X86ISA::I22$INLINE)
(X86ISA::N22-TO-I22$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I22-TO-N22$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N24P$INLINE)
(X86ISA::N24$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I24P$INLINE)
(X86ISA::I24$INLINE)
(X86ISA::N24-TO-I24$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I24-TO-N24$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N25P$INLINE)
(X86ISA::N25$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I25P$INLINE)
(X86ISA::I25$INLINE)
(X86ISA::N25-TO-I25$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I25-TO-N25$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N26P$INLINE)
(X86ISA::N26$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I26P$INLINE)
(X86ISA::I26$INLINE)
(X86ISA::N26-TO-I26$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I26-TO-N26$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N27P$INLINE)
(X86ISA::N27$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I27P$INLINE)
(X86ISA::I27$INLINE)
(X86ISA::N27-TO-I27$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I27-TO-N27$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N28P$INLINE)
(X86ISA::N28$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I28P$INLINE)
(X86ISA::I28$INLINE)
(X86ISA::N28-TO-I28$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I28-TO-N28$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N30P$INLINE)
(X86ISA::N30$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I30P$INLINE)
(X86ISA::I30$INLINE)
(X86ISA::N30-TO-I30$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I30-TO-N30$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N32P$INLINE)
(X86ISA::N32$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I32P$INLINE)
(X86ISA::I32$INLINE)
(X86ISA::N32-TO-I32$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I32-TO-N32$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N33P$INLINE)
(X86ISA::N33$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I33P$INLINE)
(X86ISA::I33$INLINE)
(X86ISA::N33-TO-I33$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I33-TO-N33$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N35P$INLINE)
(X86ISA::N35$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I35P$INLINE)
(X86ISA::I35$INLINE)
(X86ISA::N35-TO-I35$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I35-TO-N35$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N43P$INLINE)
(X86ISA::N43$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I43P$INLINE)
(X86ISA::I43$INLINE)
(X86ISA::N43-TO-I43$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I43-TO-N43$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N44P$INLINE)
(X86ISA::N44$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I44P$INLINE)
(X86ISA::I44$INLINE)
(X86ISA::N44-TO-I44$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I44-TO-N44$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N45P$INLINE)
(X86ISA::N45$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I45P$INLINE)
(X86ISA::I45$INLINE)
(X86ISA::N45-TO-I45$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I45-TO-N45$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N47P$INLINE)
(X86ISA::N47$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I47P$INLINE)
(X86ISA::I47$INLINE)
(X86ISA::N47-TO-I47$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I47-TO-N47$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N48P$INLINE)
(X86ISA::N48$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I48P$INLINE)
(X86ISA::I48$INLINE)
(X86ISA::N48-TO-I48$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I48-TO-N48$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N49P$INLINE)
(X86ISA::N49$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I49P$INLINE)
(X86ISA::I49$INLINE)
(X86ISA::N49-TO-I49$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I49-TO-N49$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N51P$INLINE)
(X86ISA::N51$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I51P$INLINE)
(X86ISA::I51$INLINE)
(X86ISA::N51-TO-I51$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I51-TO-N51$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N52P$INLINE)
(X86ISA::N52$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I52P$INLINE)
(X86ISA::I52$INLINE)
(X86ISA::N52-TO-I52$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I52-TO-N52$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N55P$INLINE)
(X86ISA::N55$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I55P$INLINE)
(X86ISA::I55$INLINE)
(X86ISA::N55-TO-I55$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I55-TO-N55$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N59P$INLINE)
(X86ISA::N59$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I59P$INLINE)
(X86ISA::I59$INLINE)
(X86ISA::N59-TO-I59$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I59-TO-N59$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N60P$INLINE)
(X86ISA::N60$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I60P$INLINE)
(X86ISA::I60$INLINE)
(X86ISA::N60-TO-I60$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I60-TO-N60$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N64P$INLINE)
(X86ISA::N64$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I64P$INLINE)
(X86ISA::I64$INLINE)
(X86ISA::N64-TO-I64$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I64-TO-N64$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N65P$INLINE)
(X86ISA::N65$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I65P$INLINE)
(X86ISA::I65$INLINE)
(X86ISA::N65-TO-I65$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I65-TO-N65$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N80P$INLINE)
(X86ISA::N80$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                    (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                    (35 7 (:DEFINITION INTEGER-RANGE-P))
                    (32 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                    (28 28
                        (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE DEFAULT-<-1))
                    (12 2
                        (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                    (10 5
                        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                    (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                    (7 7
                       (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                    (6 2
                       (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                    (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                    (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                    (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I80P$INLINE)
(X86ISA::I80$INLINE)
(X86ISA::N80-TO-I80$INLINE (116 8 (:LINEAR LOGEXT-BOUNDS))
                           (17 17 (:REWRITE DEFAULT-<-2))
                           (17 17 (:REWRITE DEFAULT-<-1))
                           (12 12
                               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                           (12 12 (:REWRITE DEFAULT-+-2))
                           (12 12 (:REWRITE DEFAULT-+-1))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (6 6
                              (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I80-TO-N80$INLINE (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
                           (14 14 (:REWRITE DEFAULT-<-2))
                           (14 14 (:REWRITE DEFAULT-<-1))
                           (8 8
                              (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
                           (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (4 4
                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N112P$INLINE)
(X86ISA::N112$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                     (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                     (35 7 (:DEFINITION INTEGER-RANGE-P))
                     (32 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                     (28 28
                         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                     (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (12 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                     (10 5
                         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                     (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                     (7 7
                        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                     (6 2
                        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                     (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I112P$INLINE)
(X86ISA::I112$INLINE)
(X86ISA::N112-TO-I112$INLINE
     (116 8 (:LINEAR LOGEXT-BOUNDS))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I112-TO-N112$INLINE
     (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N120P$INLINE)
(X86ISA::N120$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                     (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                     (35 7 (:DEFINITION INTEGER-RANGE-P))
                     (32 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                     (28 28
                         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                     (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (12 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                     (10 5
                         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                     (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                     (7 7
                        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                     (6 2
                        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                     (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I120P$INLINE)
(X86ISA::I120$INLINE)
(X86ISA::N120-TO-I120$INLINE
     (116 8 (:LINEAR LOGEXT-BOUNDS))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I120-TO-N120$INLINE
     (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N128P$INLINE)
(X86ISA::N128$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                     (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                     (35 7 (:DEFINITION INTEGER-RANGE-P))
                     (32 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                     (28 28
                         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                     (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (12 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                     (10 5
                         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                     (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                     (7 7
                        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                     (6 2
                        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                     (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I128P$INLINE)
(X86ISA::I128$INLINE)
(X86ISA::N128-TO-I128$INLINE
     (116 8 (:LINEAR LOGEXT-BOUNDS))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I128-TO-N128$INLINE
     (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N256P$INLINE)
(X86ISA::N256$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                     (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                     (35 7 (:DEFINITION INTEGER-RANGE-P))
                     (32 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                     (28 28
                         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                     (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (12 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                     (10 5
                         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                     (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                     (7 7
                        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                     (6 2
                        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                     (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I256P$INLINE)
(X86ISA::I256$INLINE)
(X86ISA::N256-TO-I256$INLINE
     (116 8 (:LINEAR LOGEXT-BOUNDS))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I256-TO-N256$INLINE
     (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::N512P$INLINE)
(X86ISA::N512$INLINE (64 8 (:REWRITE LOGHEAD-IDENTITY))
                     (42 7 (:DEFINITION UNSIGNED-BYTE-P))
                     (35 7 (:DEFINITION INTEGER-RANGE-P))
                     (32 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                     (28 28
                         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                     (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (12 2
                         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                     (10 5
                         (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                     (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                     (7 7
                        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                     (6 2
                        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                     (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(X86ISA::I512P$INLINE)
(X86ISA::I512$INLINE)
(X86ISA::N512-TO-I512$INLINE
     (116 8 (:LINEAR LOGEXT-BOUNDS))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (6 6
        (:REWRITE BITOPS::SIGNED-BYTE-P-INCR)))
(X86ISA::I512-TO-N512$INLINE
     (42 4 (:LINEAR LOGHEAD-UPPER-BOUND))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(X86ISA::TRUNC$INLINE)
(X86ISA::LIST-TO-ALIST (3 3 (:REWRITE DEFAULT-CDR))
                       (3 3 (:REWRITE DEFAULT-CAR))
                       (3 1 (:REWRITE NATP-WHEN-GTE-0))
                       (2 1 (:DEFINITION TRUE-LISTP))
                       (1 1 (:REWRITE NATP-WHEN-INTEGERP))
                       (1 1 (:REWRITE DEFAULT-<-2))
                       (1 1 (:REWRITE DEFAULT-<-1)))
(X86ISA::ALISTP-REVAPPEND
     (522 221 (:REWRITE DEFAULT-CAR))
     (505 224 (:REWRITE DEFAULT-CDR))
     (96 96 (:REWRITE CONSP-OF-REV))
     (35 35
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (32 32 (:REWRITE REV-WHEN-NOT-CONSP))
     (6 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
     (3 3 (:TYPE-PRESCRIPTION REVAPPEND)))
(X86ISA::ALISTP-OF-LIST-TO-ALIST
     (124 63 (:REWRITE DEFAULT-CAR))
     (117 56 (:REWRITE DEFAULT-CDR))
     (45 45 (:REWRITE CONSP-OF-REV))
     (17 17 (:REWRITE REV-WHEN-NOT-CONSP))
     (8 4 (:REWRITE DEFAULT-+-2))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 1 (:REWRITE FOLD-CONSTS-IN-+)))
(X86ISA::BOUNDED-INTEGER-ALISTP-MONOTONE (80 80 (:REWRITE DEFAULT-CAR))
                                         (45 45 (:REWRITE DEFAULT-<-2))
                                         (45 45 (:REWRITE DEFAULT-<-1))
                                         (12 12 (:REWRITE DEFAULT-CDR))
                                         (7 7 (:REWRITE NATP-WHEN-INTEGERP)))
(X86ISA::BOUNDED-INTEGER-ALISTP-REVAPPEND
     (2327 956 (:REWRITE DEFAULT-CDR))
     (588 575 (:REWRITE DEFAULT-<-2))
     (285 285 (:REWRITE CONSP-OF-REV))
     (167 167
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (95 95 (:REWRITE REV-WHEN-NOT-CONSP))
     (32 32
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
     (3 3 (:TYPE-PRESCRIPTION REVAPPEND)))
(X86ISA::BOUNDED-INTEGER-ALISTP-LIST-TO-ALIST
     (462 323 (:REWRITE DEFAULT-CAR))
     (359 168 (:REWRITE DEFAULT-CDR))
     (224 218 (:REWRITE DEFAULT-<-2))
     (218 218 (:REWRITE DEFAULT-<-1))
     (108 36 (:REWRITE NATP-WHEN-GTE-0))
     (95 95 (:REWRITE CONSP-OF-REV))
     (38 23 (:REWRITE DEFAULT-+-2))
     (36 36 (:REWRITE NATP-WHEN-INTEGERP))
     (28 28 (:REWRITE REV-WHEN-NOT-CONSP))
     (23 23 (:REWRITE DEFAULT-+-1))
     (8 6 (:REWRITE FOLD-CONSTS-IN-+)))
(X86ISA::LIST-TO-ARRAY (48 1 (:REWRITE ARRAY1P-CONS))
                       (42 37 (:REWRITE DEFAULT-CDR))
                       (38 27 (:REWRITE DEFAULT-CAR))
                       (24 13 (:REWRITE DEFAULT-+-2))
                       (21 21 (:TYPE-PRESCRIPTION ASSOC-KEYWORD))
                       (14 6 (:REWRITE DEFAULT-<-2))
                       (14 6 (:REWRITE DEFAULT-<-1))
                       (13 13 (:REWRITE DEFAULT-+-1))
                       (6 3 (:DEFINITION TRUE-LISTP))
                       (4 4 (:LINEAR ARRAY1P-LINEAR))
                       (4 1
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (4 1 (:DEFINITION X86ISA::LIST-TO-ALIST))
                       (2 2 (:LINEAR ARRAY2P-LINEAR))
                       (1 1
                          (:REWRITE X86ISA::BOUNDED-INTEGER-ALISTP-MONOTONE))
                       (1 1 (:DEFINITION ACONS)))
(X86ISA::INTS-TO-BOOLEANS-ACC (4 2 (:DEFINITION TRUE-LISTP))
                              (3 3 (:REWRITE DEFAULT-CDR))
                              (2 2 (:REWRITE DEFAULT-CAR)))
(X86ISA::INTS-TO-BOOLEANS)
(X86ISA::GLOBALLY-DISABLE-FN)
(X86ISA::SHOW-GLOBALLY-DISABLED-EVENTS-FN)
(X86ISA::DISABLEDP-LST)
