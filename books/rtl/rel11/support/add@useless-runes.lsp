(BEFORE-INCLUDING-ARITHMETIC-5)
(RTL::BITS-DEFAULT
 (468 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (429 3 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (426 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (173 26 (:REWRITE ACL2-NUMBERP-X))
 (164 28 (:REWRITE DEFAULT-TIMES-1))
 (163 28 (:REWRITE DEFAULT-TIMES-2))
 (153 24 (:REWRITE RATIONALP-X))
 (129 3 (:REWRITE RTL::BITS-NEG-INDICES))
 (56
  56
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (43 1 (:REWRITE RTL::INTEGERP-FL))
 (30 3 (:REWRITE DEFAULT-DIVIDE))
 (29 3 (:REWRITE DEFAULT-FLOOR-1))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:REWRITE INTEGERP-MINUS-X))
 (23 23 (:META META-INTEGERP-CORRECT))
 (20 2 (:REWRITE DEFAULT-MOD-2))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE DEFAULT-MINUS))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:REWRITE DEFAULT-PLUS-2))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (3 3 (:REWRITE DEFAULT-FLOOR-2))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|)))
(RTL::BITS-BOUNDS-<=
 (119 1 (:REWRITE ODD-EXPT-THM))
 (113 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (71 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (70
  70
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (33 1 (:REWRITE |(< (+ (- c) x) y)|))
 (31 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (29 2 (:REWRITE |(+ y (+ x z))|))
 (27 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (15 14 (:REWRITE DEFAULT-PLUS-1))
 (14 14 (:REWRITE DEFAULT-PLUS-2))
 (12 6 (:REWRITE NORMALIZE-ADDENDS))
 (9 2 (:REWRITE |(+ y x)|))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 3 (:REWRITE |(+ c (+ d x))|))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(+ 0 x)|))
 (2 2 (:DEFINITION FIX))
 (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(+ x (- x))|)))
(RTL::BITS-MOD-FL-REWRITE
 (5179 223
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4196 7 (:REWRITE RTL::MOD-DOES-NOTHING))
 (3618 102 (:LINEAR RTL::FL-DEF))
 (3284 139
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2765 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1584 15
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1312 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (1298 32 (:REWRITE RATIONALP-X))
 (1063 7 (:REWRITE CANCEL-MOD-+))
 (998 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (896
  896
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (896 896
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (896
     896
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (896 896
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (896 896
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (896 896
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (854 14 (:REWRITE ODD-EXPT-THM))
 (835 9 (:LINEAR EXPT->=-1-ONE))
 (835 9 (:LINEAR EXPT-<=-1-TWO))
 (821 9 (:LINEAR EXPT->-1-ONE))
 (821 9 (:LINEAR EXPT-<-1-TWO))
 (788 651 (:REWRITE DEFAULT-PLUS-1))
 (749 651 (:REWRITE DEFAULT-PLUS-2))
 (716 9 (:LINEAR EXPT-X->=-X))
 (716 9 (:LINEAR EXPT-X->-X))
 (714 49 (:REWRITE |(< (+ (- c) x) y)|))
 (700 7 (:REWRITE MOD-ZERO . 4))
 (671 7 (:REWRITE MOD-ZERO . 3))
 (650 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (602 7 (:REWRITE MOD-X-Y-=-X . 4))
 (601 7 (:REWRITE MOD-X-Y-=-X . 3))
 (598 232 (:REWRITE NORMALIZE-ADDENDS))
 (511 70 (:REWRITE |(< y (+ (- c) x))|))
 (485 102 (:REWRITE |(+ y x)|))
 (450 8 (:REWRITE DEFAULT-MOD-RATIO))
 (430 2 (:LINEAR RTL::MOD-BND-2))
 (420 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (420 60 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (420 60
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (420 60
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (400 50 (:REWRITE |(- (+ x y))|))
 (397 397
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (393 393
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (393 393
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (393 393
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (356 223 (:REWRITE DEFAULT-LESS-THAN-2))
 (356 38 (:REWRITE DEFAULT-TIMES-2))
 (300 139
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (255 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (255 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (255 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (255 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (253 223 (:REWRITE DEFAULT-LESS-THAN-1))
 (252 7 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (252 7
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (250 25 (:REWRITE DEFAULT-DIVIDE))
 (238 7 (:REWRITE |(integerp (- x))|))
 (230 90 (:REWRITE SIMPLIFY-SUMS-<))
 (223 223 (:REWRITE THE-FLOOR-BELOW))
 (223 223 (:REWRITE THE-FLOOR-ABOVE))
 (223 223
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (223 223
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (201 113 (:REWRITE DEFAULT-MINUS))
 (195 7 (:REWRITE |(* (- x) y)|))
 (189 7 (:REWRITE MOD-X-Y-=-X . 2))
 (188 2 (:LINEAR MOD-BOUNDS-3))
 (182 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (182 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (181 181
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (139 139
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (139 139 (:REWRITE INTEGERP-<-CONSTANT))
 (139 139 (:REWRITE CONSTANT-<-INTEGERP))
 (139 139
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (139 139
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (139 139
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (139 139
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (139 139 (:REWRITE |(< c (- x))|))
 (139 139
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (139 139
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (139 139
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (139 139
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (139 139 (:REWRITE |(< (/ x) (/ y))|))
 (139 139 (:REWRITE |(< (- x) c)|))
 (139 139 (:REWRITE |(< (- x) (- y))|))
 (138 102 (:DEFINITION FIX))
 (121 15
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (119 7
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (119 7 (:REWRITE MOD-CANCEL-*-CONST))
 (119 7
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (119 7
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (111 1 (:REWRITE MOD-ZERO . 1))
 (105 105 (:REWRITE |(< x (+ c/d y))|))
 (104 4 (:LINEAR MOD-BOUNDS-2))
 (102 102 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (100 50 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (91 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (80 8 (:REWRITE DEFAULT-MOD-2))
 (76 76 (:REWRITE FOLD-CONSTS-IN-+))
 (69 51 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (65 65 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (63 63 (:REWRITE |(< (+ c/d x) y)|))
 (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (60 60
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (60 60 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (60 60
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (60 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (52 52 (:REWRITE REDUCE-INTEGERP-+))
 (52 52 (:REWRITE INTEGERP-MINUS-X))
 (52 52 (:META META-INTEGERP-CORRECT))
 (52 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (51 51 (:REWRITE |(+ x (- x))|))
 (51 51 (:LINEAR RTL::N<=FL-LINEAR))
 (43 1 (:REWRITE RTL::INTEGERP-FL))
 (42 42 (:REWRITE |(< 0 (* x y))|))
 (42 3 (:REWRITE |(* y x)|))
 (33 15 (:REWRITE |(equal (- x) (- y))|))
 (32 32 (:REWRITE REDUCE-RATIONALP-+))
 (32 32 (:REWRITE REDUCE-RATIONALP-*))
 (32 32 (:REWRITE RATIONALP-MINUS-X))
 (32 32 (:REWRITE |(< (* x y) 0)|))
 (32 32 (:META META-RATIONALP-CORRECT))
 (29 29 (:REWRITE DEFAULT-EXPT-2))
 (29 29 (:REWRITE DEFAULT-EXPT-1))
 (29 29 (:REWRITE |(expt 1/c n)|))
 (29 29 (:REWRITE |(expt (- x) n)|))
 (27 1 (:REWRITE MOD-ZERO . 2))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (25 25 (:REWRITE |(- (- x))|))
 (24 15 (:REWRITE |(equal (- x) c)|))
 (22 2
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (21 21 (:REWRITE |(< 0 (/ x))|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (15 15 (:REWRITE |(equal c (/ x))|))
 (15 15 (:REWRITE |(equal c (- x))|))
 (15 15 (:REWRITE |(equal (/ x) c)|))
 (15 15 (:REWRITE |(equal (/ x) (/ y))|))
 (15 8 (:REWRITE DEFAULT-MOD-1))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (9 9 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:LINEAR EXPT->=-1-TWO))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<=-1-ONE))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (7 7 (:REWRITE |(mod x (- y))| . 3))
 (7 7 (:REWRITE |(mod x (- y))| . 2))
 (7 7 (:REWRITE |(mod x (- y))| . 1))
 (7 7
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (7 7 (:REWRITE |(mod (- x) y)| . 3))
 (7 7 (:REWRITE |(mod (- x) y)| . 2))
 (7 7 (:REWRITE |(mod (- x) y)| . 1))
 (7 7
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (7 7 (:REWRITE |(- (* c x))|))
 (7 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:LINEAR RTL::MOD-BND-3))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(* 0 x)|)))
(RTL::FL-{X+Y+Z}/M
     (63986 471 (:REWRITE DEFAULT-PLUS-2))
     (60007 60007
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (60007 60007
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (60007 60007
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (28920 5784 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (28920 5784 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (27655 471 (:REWRITE DEFAULT-PLUS-1))
     (25992 5784
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (25992 5784
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (15612 5 (:REWRITE FLOOR-=-X/Y . 4))
     (13861 1645
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (13861 1645
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (13861 1645
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (13861 1645
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (13861 1645
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (11568 5784 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (10917 254 (:REWRITE CANCEL-MOD-+))
     (10553 280
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10553 280
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9241 254 (:REWRITE MOD-X-Y-=-X . 4))
     (9241 254 (:REWRITE MOD-X-Y-=-X . 3))
     (8938 254 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (8305 8305
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (8305 8305
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (8162 254 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (7753 1645
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6390 1642 (:REWRITE DEFAULT-LESS-THAN-1))
     (6321 1639
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6217 242 (:REWRITE RTL::MOD-DOES-NOTHING))
     (6150 254 (:REWRITE MOD-ZERO . 3))
     (6107 1639
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5784 5784
           (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (5784 5784 (:TYPE-PRESCRIPTION NATP))
     (5784 5784 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (5784 5784 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (5784 5784
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (5784 5784
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (5784 5784
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (5784 5784
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (5784 5784
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (5784 5784
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (5736 3240 (:REWRITE DEFAULT-TIMES-2))
     (5731 1639
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5024 314 (:REWRITE |(integerp (- x))|))
     (4957 254 (:REWRITE MOD-ZERO . 4))
     (4896 48 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4762 316 (:REWRITE |(* (- x) y)|))
     (4353 57 (:REWRITE FLOOR-ZERO . 3))
     (4148 3240 (:REWRITE DEFAULT-TIMES-1))
     (3618 1098
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3530 57 (:REWRITE CANCEL-FLOOR-+))
     (3416 254 (:REWRITE DEFAULT-MOD-RATIO))
     (3175 1639 (:REWRITE SIMPLIFY-SUMS-<))
     (2700 940 (:REWRITE REDUCE-INTEGERP-+))
     (2603 57 (:REWRITE FLOOR-ZERO . 5))
     (2603 57 (:REWRITE FLOOR-ZERO . 4))
     (2575 1639
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2552 57 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (2418 78 (:LINEAR RTL::MOD-BND-2))
     (2309 57 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (2262 940 (:META META-INTEGERP-CORRECT))
     (1872 78 (:LINEAR MOD-BOUNDS-3))
     (1794 1642 (:REWRITE DEFAULT-LESS-THAN-2))
     (1764 57 (:REWRITE FLOOR-=-X/Y . 2))
     (1748 57 (:REWRITE FLOOR-=-X/Y . 3))
     (1718 334 (:REWRITE DEFAULT-MINUS))
     (1642 1642 (:REWRITE THE-FLOOR-BELOW))
     (1642 1642 (:REWRITE THE-FLOOR-ABOVE))
     (1641 1641
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1641 1641
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1639 1639 (:REWRITE INTEGERP-<-CONSTANT))
     (1639 1639 (:REWRITE CONSTANT-<-INTEGERP))
     (1639 1639
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1639 1639
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1639 1639
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1639 1639
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1639 1639 (:REWRITE |(< c (- x))|))
     (1639 1639
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1639 1639
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1639 1639
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1639 1639 (:REWRITE |(< (/ x) (/ y))|))
     (1639 1639 (:REWRITE |(< (- x) c)|))
     (1639 1639 (:REWRITE |(< (- x) (- y))|))
     (1332 942 (:REWRITE INTEGERP-MINUS-X))
     (1326 254 (:REWRITE MOD-X-Y-=-X . 2))
     (1326 254
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (1326 254
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (1300 1300
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1274 254 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (1274 254 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1274 254
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1222 254
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1198 254 (:REWRITE MOD-CANCEL-*-CONST))
     (1131 57 (:REWRITE DEFAULT-FLOOR-RATIO))
     (1077 1077
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1077 1077 (:REWRITE DEFAULT-DIVIDE))
     (909 733
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (909 733
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (780 156 (:LINEAR MOD-BOUNDS-2))
     (733 733 (:REWRITE |(< (/ x) 0)|))
     (733 733 (:REWRITE |(< (* x y) 0)|))
     (530 14 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (474 14 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (423 24 (:REWRITE |(floor x 1)|))
     (369 317
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (369 317
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (366 366
          (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (320 320 (:REWRITE |(- (* c x))|))
     (317 317 (:REWRITE |(< 0 (/ x))|))
     (317 317 (:REWRITE |(< 0 (* x y))|))
     (306 254 (:REWRITE DEFAULT-MOD-1))
     (301 57 (:REWRITE FLOOR-ZERO . 2))
     (301 57 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (301 57 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (280 280
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (280 280
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (280 280
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (280 280 (:REWRITE |(equal c (/ x))|))
     (280 280 (:REWRITE |(equal c (- x))|))
     (280 280 (:REWRITE |(equal (/ x) c)|))
     (280 280 (:REWRITE |(equal (/ x) (/ y))|))
     (280 280 (:REWRITE |(equal (- x) c)|))
     (280 280 (:REWRITE |(equal (- x) (- y))|))
     (277 57 (:REWRITE FLOOR-CANCEL-*-CONST))
     (263 251
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (260 8 (:REWRITE |(- (+ x y))|))
     (254 254
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (254 254 (:REWRITE DEFAULT-MOD-2))
     (254 254 (:REWRITE |(mod x (- y))| . 3))
     (254 254 (:REWRITE |(mod x (- y))| . 2))
     (254 254 (:REWRITE |(mod x (- y))| . 1))
     (254 254
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (254 254 (:REWRITE |(mod (- x) y)| . 3))
     (254 254 (:REWRITE |(mod (- x) y)| . 2))
     (254 254 (:REWRITE |(mod (- x) y)| . 1))
     (243 243
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (240 60 (:REWRITE RATIONALP-X))
     (221 57
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (216 216
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (205 12 (:REWRITE |(mod x 1)|))
     (169 57 (:REWRITE DEFAULT-FLOOR-1))
     (137 57
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (137 57
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (124 44
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (109 57
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (104 104
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (100 100 (:REWRITE FOLD-CONSTS-IN-+))
     (78 78 (:LINEAR RTL::MOD-BND-3))
     (67 67 (:REWRITE |(< (+ c/d x) y)|))
     (65 65 (:REWRITE |(< (+ (- c) x) y)|))
     (63 63 (:REWRITE |arith (* c (* d x))|))
     (60 60 (:REWRITE REDUCE-RATIONALP-+))
     (60 60 (:REWRITE REDUCE-RATIONALP-*))
     (60 60 (:REWRITE RATIONALP-MINUS-X))
     (60 60 (:META META-RATIONALP-CORRECT))
     (57 57 (:REWRITE DEFAULT-FLOOR-2))
     (57 57 (:REWRITE |(floor x (- y))| . 2))
     (57 57 (:REWRITE |(floor x (- y))| . 1))
     (57 57 (:REWRITE |(floor (- x) y)| . 2))
     (57 57 (:REWRITE |(floor (- x) y)| . 1))
     (48 3 (:REWRITE |(floor (+ x r) i)|))
     (30 30 (:REWRITE |(equal (+ (- c) x) y)|))
     (30 6 (:REWRITE |(- (- x))|))
     (29 29
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (29 29
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (27 27 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (25 5
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (23 23 (:REWRITE |arith (* (- x) y)|))
     (21 21
         (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (21 21
         (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (21 21
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (21 21
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (16 16
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (11 11 (:REWRITE |arith (+ c (+ d x))|))
     (11 11 (:REWRITE |(equal (* x y) 0)|))
     (8 8
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (8 8
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (8 8
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (8 8
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (8 8
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (3 3
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (3 3
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2)))
(RTL::FL-{X+Y}/M (984 492 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
                 (492 492
                      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
                 (492 492 (:TYPE-PRESCRIPTION NATP))
                 (492 492
                      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
                 (239 41 (:REWRITE DEFAULT-+-2))
                 (74 41 (:REWRITE DEFAULT-+-1))
                 (67 27 (:REWRITE DEFAULT-<-1))
                 (39 13 (:REWRITE RTL::MOD-DOES-NOTHING))
                 (34 34 (:REWRITE DEFAULT-*-2))
                 (34 34 (:REWRITE DEFAULT-*-1))
                 (27 27 (:REWRITE DEFAULT-<-2))
                 (20 20 (:REWRITE RTL::FL+INT-REWRITE))
                 (18 18 (:LINEAR RTL::FL-MONOTONE-LINEAR))
                 (15 5 (:LINEAR RTL::MOD-BND-2))
                 (13 13 (:REWRITE DEFAULT-UNARY-/))
                 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
                 (9 9 (:LINEAR RTL::N<=FL-LINEAR))
                 (5 5 (:LINEAR RTL::MOD-BND-3)))
(RTL::LEMMA (381 381
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
            (381 381
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
            (381 381
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
            (171 15 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
            (127 15
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
            (127 15
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
            (127 15
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
            (75 15 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
            (75 15 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
            (75 15
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
            (56 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
            (28 4
                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
            (28 4 (:REWRITE FLOOR-=-X/Y . 2))
            (28 4 (:REWRITE DEFAULT-FLOOR-RATIO))
            (22 22 (:REWRITE DEFAULT-TIMES-2))
            (22 22 (:REWRITE DEFAULT-TIMES-1))
            (20 4 (:REWRITE FLOOR-ZERO . 5))
            (20 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
            (20 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
            (20 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
            (20 4 (:REWRITE FLOOR-=-X/Y . 3))
            (8 8 (:REWRITE THE-FLOOR-BELOW))
            (8 8 (:REWRITE THE-FLOOR-ABOVE))
            (8 8
               (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
            (8 8
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
            (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
            (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
            (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
            (7 7 (:REWRITE |(< (/ x) y) with (< x 0)|))
            (5 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
            (4 4 (:REWRITE DEFAULT-FLOOR-2))
            (4 4 (:REWRITE DEFAULT-FLOOR-1))
            (4 4 (:REWRITE |(floor x 1)|))
            (2 2 (:REWRITE DEFAULT-PLUS-2))
            (2 2 (:REWRITE DEFAULT-PLUS-1))
            (1 1 (:REWRITE SIMPLIFY-SUMS-<))
            (1 1
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
            (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
            (1 1 (:REWRITE REDUCE-INTEGERP-+))
            (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
            (1 1
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (1 1
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (1 1 (:REWRITE NORMALIZE-ADDENDS))
            (1 1 (:REWRITE INTEGERP-MINUS-X))
            (1 1 (:REWRITE INTEGERP-<-CONSTANT))
            (1 1 (:REWRITE DEFAULT-DIVIDE))
            (1 1 (:REWRITE CONSTANT-<-INTEGERP))
            (1 1
               (:REWRITE |(< c (/ x)) positive c --- present in goal|))
            (1 1
               (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
            (1 1
               (:REWRITE |(< c (/ x)) negative c --- present in goal|))
            (1 1
               (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
            (1 1 (:REWRITE |(< c (- x))|))
            (1 1
               (:REWRITE |(< (/ x) c) positive c --- present in goal|))
            (1 1
               (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
            (1 1
               (:REWRITE |(< (/ x) c) negative c --- present in goal|))
            (1 1
               (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
            (1 1 (:REWRITE |(< (/ x) (/ y))|))
            (1 1 (:REWRITE |(< (- x) c)|))
            (1 1 (:REWRITE |(< (- x) (- y))|))
            (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::FL-{X+Y+CIN}/M (1630 815 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
                     (815 815 (:TYPE-PRESCRIPTION NATP))
                     (815 815
                          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
                     (657 288 (:REWRITE DEFAULT-+-2))
                     (368 288 (:REWRITE DEFAULT-+-1))
                     (199 153 (:REWRITE DEFAULT-<-1))
                     (186 186 (:REWRITE DEFAULT-*-2))
                     (186 186 (:REWRITE DEFAULT-*-1))
                     (153 153 (:REWRITE DEFAULT-<-2))
                     (130 130 (:LINEAR RTL::FL-MONOTONE-LINEAR))
                     (70 70 (:REWRITE DEFAULT-UNARY-/))
                     (66 22 (:LINEAR RTL::MOD-BND-2))
                     (65 65 (:LINEAR RTL::N<=FL-LINEAR))
                     (24 6 (:REWRITE RATIONALP-+))
                     (22 22 (:LINEAR RTL::MOD-BND-3)))
(RTL::BITN-X+Y+CIN
 (2454 6 (:REWRITE RTL::NEG-BITN-0))
 (1964 6 (:REWRITE RTL::BVECP-BITN-0))
 (1792 256 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1792 256 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1704 6 (:REWRITE RTL::MOD-DOES-NOTHING))
 (1612 103 (:REWRITE DEFAULT-PLUS-2))
 (1430 189
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1328 4 (:REWRITE RTL::BITS-TAIL))
 (1192 256
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1192 256
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1148
   1148
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1148
  1148
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1148
      1148
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1148
     1148
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1148 1148
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1148 1148
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1110 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (976 976
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (976 976
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (968 968
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (968 968
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (968 968
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (885 9 (:REWRITE RTL::INTEGERP-FL))
 (870 6 (:REWRITE CANCEL-MOD-+))
 (750 30 (:LINEAR EXPT-<=-1-TWO))
 (726 30 (:LINEAR EXPT->-1-ONE))
 (697 103 (:REWRITE DEFAULT-PLUS-1))
 (662 189
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (630 30 (:LINEAR EXPT-X->=-X))
 (630 30 (:LINEAR EXPT-X->-X))
 (624 187 (:REWRITE SIMPLIFY-SUMS-<))
 (531 97 (:REWRITE DEFAULT-TIMES-2))
 (492 6 (:REWRITE MOD-ZERO . 3))
 (475 196 (:REWRITE DEFAULT-LESS-THAN-2))
 (450 60
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (420 30 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (420 30 (:LINEAR EXPT->=-1-ONE))
 (418 12 (:REWRITE DEFAULT-MOD-RATIO))
 (415 25 (:REWRITE ODD-EXPT-THM))
 (390 196 (:REWRITE DEFAULT-LESS-THAN-1))
 (378 196
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (378 6 (:REWRITE RTL::FL+INT-REWRITE))
 (324 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (309 57 (:META META-INTEGERP-CORRECT))
 (276 6 (:REWRITE MOD-X-Y-=-X . 4))
 (276 6 (:REWRITE MOD-X-Y-=-X . 3))
 (258 6 (:REWRITE |(integerp (- x))|))
 (256 256 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (256 256
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (256 256
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (256 256
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (245 97 (:REWRITE DEFAULT-TIMES-1))
 (240 24 (:REWRITE DEFAULT-DIVIDE))
 (204 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (204 6
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (200 100 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (196 196 (:REWRITE THE-FLOOR-BELOW))
 (196 196 (:REWRITE THE-FLOOR-ABOVE))
 (196 196
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (196 196
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (190 190
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (190 190 (:REWRITE INTEGERP-<-CONSTANT))
 (190 190 (:REWRITE CONSTANT-<-INTEGERP))
 (190 190
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (190 190
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (190 190
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (190 190
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (190 190 (:REWRITE |(< c (- x))|))
 (190 190
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (190 190
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (190 190
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (190 190
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (190 190 (:REWRITE |(< (/ x) (/ y))|))
 (190 190 (:REWRITE |(< (- x) c)|))
 (190 190 (:REWRITE |(< (- x) (- y))|))
 (184 6 (:REWRITE RTL::NEG-BITN-1))
 (174 6 (:REWRITE MOD-ZERO . 4))
 (171 39 (:REWRITE DEFAULT-MINUS))
 (168 6 (:REWRITE |(* (- x) y)|))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (150 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (150 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (150 6 (:REWRITE MOD-X-Y-=-X . 2))
 (149 149 (:REWRITE DEFAULT-EXPT-2))
 (149 149 (:REWRITE DEFAULT-EXPT-1))
 (149 149 (:REWRITE |(expt 1/c n)|))
 (149 149 (:REWRITE |(expt (- x) n)|))
 (113 47 (:REWRITE NORMALIZE-ADDENDS))
 (102 102 (:TYPE-PRESCRIPTION NATP))
 (100 100
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (100 100 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (100 100
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (100 100 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (100 100 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (100 100
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (96 6
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (96 6 (:REWRITE MOD-CANCEL-*-CONST))
 (96 6
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (96 6
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (90 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (84 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (84 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (70 70
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (67 67
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (67 67
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (67 67 (:REWRITE |(< 0 (/ x))|))
 (67 67 (:REWRITE |(< 0 (* x y))|))
 (66 12 (:REWRITE DEFAULT-MOD-2))
 (60 60
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (60 60
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (60 60
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (57 57 (:REWRITE REDUCE-INTEGERP-+))
 (57 57 (:REWRITE INTEGERP-MINUS-X))
 (50 2 (:REWRITE SUM-IS-EVEN . 2))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (41 41 (:REWRITE |(< (* x y) 0)|))
 (40 4 (:DEFINITION FIX))
 (36 6 (:REWRITE DEFAULT-LOGXOR-2))
 (35 35 (:REWRITE |(< (/ x) 0)|))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (30 30 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (30 30 (:LINEAR EXPT-LINEAR-UPPER-<))
 (30 30 (:LINEAR EXPT-LINEAR-LOWER-<))
 (30 30 (:LINEAR EXPT->=-1-TWO))
 (30 30 (:LINEAR EXPT->-1-TWO))
 (30 30 (:LINEAR EXPT-<=-1-ONE))
 (30 30 (:LINEAR EXPT-<-1-TWO))
 (30 30 (:LINEAR EXPT-<-1-ONE))
 (26 6 (:REWRITE DEFAULT-LOGXOR-1))
 (22 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (22 12
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (20 12 (:REWRITE DEFAULT-MOD-1))
 (20 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (18 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (16 16 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (12 12
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (12 12 (:REWRITE |(equal c (/ x))|))
 (12 12 (:REWRITE |(equal c (- x))|))
 (12 12 (:REWRITE |(equal (/ x) c)|))
 (12 12 (:REWRITE |(equal (/ x) (/ y))|))
 (12 12 (:REWRITE |(equal (- x) c)|))
 (12 12 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6 6
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE RTL::BITN-NEG))
 (6 6 (:REWRITE |(mod x 2)| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 3))
 (6 6 (:REWRITE |(mod x (- y))| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 1))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(mod (- x) y)| . 3))
 (6 6 (:REWRITE |(mod (- x) y)| . 2))
 (6 6 (:REWRITE |(mod (- x) y)| . 1))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(- (* c x))|))
 (4 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(+ x (- x))|)))
(RTL::BITN-X+Y (735 24 (:REWRITE RTL::NEG-BITN-0))
               (222 10 (:REWRITE RTL::BITS-TAIL-GEN))
               (198 66 (:REWRITE DEFAULT-*-2))
               (155 149 (:REWRITE DEFAULT-+-2))
               (155 149 (:REWRITE DEFAULT-+-1))
               (154 112 (:REWRITE DEFAULT-<-2))
               (134 38 (:REWRITE FOLD-CONSTS-IN-+))
               (122 112 (:REWRITE DEFAULT-<-1))
               (80 10 (:REWRITE RTL::BITS-TAIL))
               (72 24 (:REWRITE RTL::NEG-BITN-1))
               (72 24 (:REWRITE RTL::BVECP-BITN-0))
               (66 66 (:REWRITE DEFAULT-*-1))
               (40 40 (:REWRITE ZIP-OPEN))
               (33 15 (:REWRITE DEFAULT-UNARY-MINUS))
               (27 9 (:REWRITE RTL::BITN-BVECP-1))
               (24 24 (:REWRITE RTL::BITN-NEG))
               (12 10 (:REWRITE RTL::BITS-NEG-INDICES))
               (1 1 (:TYPE-PRESCRIPTION NATP)))
(RTL::HALF-ADDER (4 4 (:REWRITE DEFAULT-+-2))
                 (4 4 (:REWRITE DEFAULT-+-1)))
(RTL::LEMMA (2856 2856
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (2856 2856
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (2856 2856
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (2856 2856
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (1068 124 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
            (1068 124
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
            (1068 124
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
            (1068 124
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
            (1068 124
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
            (620 124 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
            (620 124 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
            (620 124 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
            (620 124
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
            (619 619
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
            (619 619
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
            (574 219 (:REWRITE DEFAULT-PLUS-2))
            (562 562
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
            (463 187 (:REWRITE DEFAULT-TIMES-2))
            (398 219 (:REWRITE DEFAULT-PLUS-1))
            (284 52
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
            (214 14 (:REWRITE DEFAULT-FLOOR-RATIO))
            (207 187 (:REWRITE DEFAULT-TIMES-1))
            (200 22 (:REWRITE |(* y x)|))
            (147 36
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (147 36
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (138 2 (:REWRITE |(not (equal x (/ y)))|))
            (138 2 (:REWRITE |(equal x (/ y))|))
            (121 121
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (111 111
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (92 40 (:REWRITE |(equal (- x) c)|))
            (70 2
                (:REWRITE |(not (equal x (- (/ y))))|))
            (70 2 (:REWRITE |(equal x (- (/ y)))|))
            (56 52
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
            (40 40 (:REWRITE |(equal c (/ x))|))
            (40 40 (:REWRITE |(equal c (- x))|))
            (40 40 (:REWRITE |(equal (/ x) c)|))
            (40 40 (:REWRITE |(equal (/ x) (/ y))|))
            (40 40 (:REWRITE |(equal (- x) (- y))|))
            (38 38 (:REWRITE REDUCE-INTEGERP-+))
            (38 38 (:REWRITE INTEGERP-MINUS-X))
            (38 38 (:META META-INTEGERP-CORRECT))
            (36 36
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
            (34 14 (:REWRITE DEFAULT-FLOOR-1))
            (28 28 (:REWRITE |(equal (+ (- c) x) y)|))
            (24 4 (:REWRITE |(* c (* d x))|))
            (23 23 (:REWRITE LOGAND-CONSTANT-MASK))
            (14 14 (:REWRITE DEFAULT-FLOOR-2))
            (14 14 (:REWRITE |(floor x 2)| . 2))
            (12 12 (:REWRITE |(* (- x) y)|))
            (11 11 (:REWRITE FOLD-CONSTS-IN-+))
            (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
            (8 8 (:REWRITE DEFAULT-MINUS))
            (8 4 (:REWRITE |(* -1 x)|))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 5))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 4))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 3))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 2))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
            (4 4
               (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2))
            (4 4 (:REWRITE |(- (- x))|))
            (4 4 (:REWRITE |(* x (- y))|))
            (3 3
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
            (2 2 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
            (2 2 (:TYPE-PRESCRIPTION ABS))
            (2 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3)))
(RTL::ADD-2 (22 22 (:REWRITE DEFAULT-+-2))
            (22 22 (:REWRITE DEFAULT-+-1))
            (5 5 (:REWRITE ZIP-OPEN))
            (4 4 (:REWRITE FOLD-CONSTS-IN-+))
            (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
            (2 2 (:REWRITE DEFAULT-*-2))
            (2 2 (:REWRITE DEFAULT-*-1)))
(RTL::FULL-ADDER (42 42 (:REWRITE DEFAULT-+-2))
                 (42 42 (:REWRITE DEFAULT-+-1))
                 (21 21 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::MEASURE-LEMMA1
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (161 55 (:REWRITE DEFAULT-LESS-THAN-2))
     (138 62 (:REWRITE DEFAULT-PLUS-1))
     (134 62 (:REWRITE DEFAULT-PLUS-2))
     (103 55 (:REWRITE DEFAULT-LESS-THAN-1))
     (93 93 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (70 62 (:REWRITE DEFAULT-TIMES-2))
     (63 62 (:REWRITE DEFAULT-TIMES-1))
     (55 55 (:REWRITE THE-FLOOR-BELOW))
     (55 55 (:REWRITE THE-FLOOR-ABOVE))
     (48 40
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (48 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (41 15 (:REWRITE DEFAULT-MINUS))
     (40 40
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (37 37
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (36 36 (:REWRITE |(< (/ x) (/ y))|))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (35 34 (:REWRITE INTEGERP-<-CONSTANT))
     (34 34
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (34 34 (:REWRITE CONSTANT-<-INTEGERP))
     (34 34 (:REWRITE |(< (- x) c)|))
     (33 33 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (33 33
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (25 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (21 21 (:REWRITE |(< (* x y) 0)|))
     (19 19 (:REWRITE |(< (/ x) 0)|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (15 15 (:REWRITE REDUCE-INTEGERP-+))
     (15 15 (:REWRITE INTEGERP-MINUS-X))
     (15 15 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 1 (:DEFINITION LENGTH))
     (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (7 1 (:REWRITE |(* (if a b c) x)|))
     (7 1 (:DEFINITION LEN))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE |(* (- x) y)|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (2 2
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:TYPE-PRESCRIPTION LEN))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE DEFAULT-REALPART))
     (1 1 (:REWRITE DEFAULT-IMAGPART))
     (1 1 (:REWRITE DEFAULT-COERCE-2))
     (1 1 (:REWRITE DEFAULT-COERCE-1))
     (1 1 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::MEASURE-LEMMA2
     (212 63 (:REWRITE DEFAULT-LESS-THAN-1))
     (182 66 (:REWRITE DEFAULT-PLUS-2))
     (166 66 (:REWRITE DEFAULT-PLUS-1))
     (154 154 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (144 144
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (144 144
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (144 144
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (88 1
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (84 72 (:REWRITE DEFAULT-TIMES-2))
     (82 63 (:REWRITE DEFAULT-LESS-THAN-2))
     (76 72 (:REWRITE DEFAULT-TIMES-1))
     (75 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (63 63 (:REWRITE THE-FLOOR-BELOW))
     (63 63 (:REWRITE THE-FLOOR-ABOVE))
     (62 48
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (62 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (51 25 (:REWRITE DEFAULT-MINUS))
     (51 2 (:REWRITE |(* (* x y) z)|))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (43 43 (:REWRITE |(< (/ x) (/ y))|))
     (42 42
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (42 42
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (42 42
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (42 42
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (42 42
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (42 42
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (42 42
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (42 42
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (36 36
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (36 36 (:REWRITE INTEGERP-<-CONSTANT))
     (36 36 (:REWRITE CONSTANT-<-INTEGERP))
     (34 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (30 30
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (22 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE |(< (+ c/d x) y)|))
     (16 16 (:REWRITE |(< (+ (- c) x) y)|))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (15 15 (:REWRITE |(* (- x) y)|))
     (14 14 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (14 14 (:TYPE-PRESCRIPTION ABS))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 4 (:REWRITE |(* -1 x)|))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (5 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (3 3 (:REWRITE ZIP-OPEN))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (2 2
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
     (2 2 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::MY-INDUCT (35 14 (:REWRITE DEFAULT-+-2))
                (28 14 (:REWRITE DEFAULT-+-1))
                (12 3 (:REWRITE DEFAULT-<-2))
                (12 3 (:REWRITE DEFAULT-<-1))
                (9 9 (:REWRITE ZIP-OPEN))
                (7 7 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::LEMMA
     (105415 247 (:LINEAR LOGIOR-BOUNDS-POS . 2))
     (105415 247 (:LINEAR LOGIOR-BOUNDS-POS . 1))
     (95645 247 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (92056 2344 (:LINEAR RTL::LOGAND-BND))
     (88187 247 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (57961 729 (:REWRITE |(< (logand x y) 0)|))
     (46836 1172 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (46836 1172 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (44980 1172 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (44980 1172 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (38711 9183
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (37096 9986 (:REWRITE THE-FLOOR-ABOVE))
     (34140 60 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (27409 27409
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (27409 27409
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (19551 19551
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (19551 19551
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (19551 19551
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (19551 19551
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (18046 18046
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (18046 18046
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (18046 18046
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (17920 1711 (:REWRITE DEFAULT-PLUS-2))
     (16993 9041
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (12515 12387
            (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (12515 12387
            (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (12515 12387
            (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (12217 1711 (:REWRITE DEFAULT-PLUS-1))
     (12016 48 (:REWRITE |(< (+ c/d x) y)|))
     (10479 9009
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10479 9009
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10421 9215 (:REWRITE DEFAULT-LESS-THAN-2))
     (9986 9986 (:REWRITE THE-FLOOR-BELOW))
     (9727 9215 (:REWRITE DEFAULT-LESS-THAN-1))
     (9426 3075 (:REWRITE DEFAULT-TIMES-2))
     (9141 9041
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9009 9009 (:REWRITE SIMPLIFY-SUMS-<))
     (9009 9009
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9009 9009 (:REWRITE INTEGERP-<-CONSTANT))
     (9009 9009 (:REWRITE CONSTANT-<-INTEGERP))
     (9009 9009
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9009 9009
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9009 9009
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9009 9009
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9009 9009 (:REWRITE |(< c (- x))|))
     (9009 9009
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9009 9009
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9009 9009
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9009 9009
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9009 9009 (:REWRITE |(< (/ x) (/ y))|))
     (9009 9009 (:REWRITE |(< (- x) c)|))
     (9009 9009 (:REWRITE |(< (- x) (- y))|))
     (8806 8806 (:REWRITE |(< (* x y) 0)|))
     (8642 8642
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8642 8642
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8642 8642 (:REWRITE |(< (/ x) 0)|))
     (7650 862 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (7650 862
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (7650 862
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (7650 862
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (7650 862
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (5992 12 (:REWRITE |(< (logior x y) 0)|))
     (5884 5884
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4310 862 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (4310 862 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (4310 862 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (4310 862
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (4000 16 (:REWRITE |(< x (+ c/d y))|))
     (3528 252
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3528 252
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3510 60 (:REWRITE FLOOR-ZERO . 3))
     (3419 3075 (:REWRITE DEFAULT-TIMES-1))
     (3180 60 (:REWRITE CANCEL-FLOOR-+))
     (3110 80 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2712 508 (:REWRITE |(* y x)|))
     (2308 116 (:REWRITE DEFAULT-FLOOR-RATIO))
     (2230 850 (:REWRITE INTEGERP-MINUS-X))
     (2041 2041
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2040 60 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1760 60 (:REWRITE FLOOR-ZERO . 5))
     (1760 60 (:REWRITE FLOOR-ZERO . 4))
     (1560 60 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1320 60 (:REWRITE FLOOR-=-X/Y . 3))
     (1320 60 (:REWRITE FLOOR-=-X/Y . 2))
     (1196 116 (:REWRITE |(floor x 2)| . 2))
     (1056 156 (:REWRITE |(* (- x) y)|))
     (1038 288
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1002 1002
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (790 790 (:REWRITE REDUCE-INTEGERP-+))
     (790 790 (:META META-INTEGERP-CORRECT))
     (780 30 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (660 30 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (630 150 (:REWRITE DEFAULT-MINUS))
     (618 6 (:REWRITE |(equal x (/ y))|))
     (540 120 (:REWRITE |(- (* c x))|))
     (477 477 (:REWRITE LOGAND-CONSTANT-MASK))
     (460 116 (:REWRITE DEFAULT-FLOOR-1))
     (390 258 (:REWRITE |(equal (- x) c)|))
     (327 327 (:REWRITE |(< 0 (* x y))|))
     (312 288
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (300 60 (:REWRITE FLOOR-ZERO . 2))
     (300 60 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (300 60 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (300 60
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (300 60
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (294 6 (:REWRITE |(equal x (- (/ y)))|))
     (285 285
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (285 285
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (285 285 (:REWRITE |(< 0 (/ x))|))
     (260 60 (:REWRITE FLOOR-CANCEL-*-CONST))
     (258 258 (:REWRITE |(equal c (/ x))|))
     (258 258 (:REWRITE |(equal c (- x))|))
     (258 258 (:REWRITE |(equal (/ x) c)|))
     (258 258 (:REWRITE |(equal (/ x) (/ y))|))
     (258 258 (:REWRITE |(equal (- x) (- y))|))
     (258 258 (:REWRITE |(equal (+ (- c) x) y)|))
     (254 254 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (254 254 (:TYPE-PRESCRIPTION ABS))
     (252 252
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (201 201 (:REWRITE FOLD-CONSTS-IN-+))
     (180 6 (:REWRITE |(not (equal x (/ y)))|))
     (180 6
          (:REWRITE |(not (equal x (- (/ y))))|))
     (166 166
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (116 116 (:REWRITE DEFAULT-FLOOR-2))
     (111 111 (:REWRITE |(logior c d x)|))
     (72 12 (:REWRITE |(* c (* d x))|))
     (60 60
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (60 60 (:REWRITE |(floor x (- y))| . 2))
     (60 60 (:REWRITE |(floor x (- y))| . 1))
     (60 60
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (60 60
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (60 60 (:REWRITE |(floor (- x) y)| . 2))
     (60 60 (:REWRITE |(floor (- x) y)| . 1))
     (60 60
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (54 6 (:REWRITE |(- (+ x y))|))
     (30 30 (:REWRITE |(+ x (- x))|))
     (26 26
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (24 12 (:REWRITE |(* -1 x)|))
     (12 12 (:REWRITE |(- (- x))|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE |(* x (- y))|)))
(RTL::ADD-3 (57 27 (:REWRITE DEFAULT-+-2))
            (51 27 (:REWRITE DEFAULT-+-1))
            (24 12 (:REWRITE DEFAULT-*-2))
            (12 12 (:REWRITE DEFAULT-*-1))
            (10 10 (:REWRITE ZIP-OPEN))
            (6 6 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::PLUS-LOGIOR-LOGAND (95 57 (:REWRITE DEFAULT-+-2))
                         (73 57 (:REWRITE DEFAULT-+-1))
                         (41 24 (:REWRITE DEFAULT-UNARY-MINUS))
                         (24 12 (:REWRITE DEFAULT-*-2))
                         (13 13 (:REWRITE FOLD-CONSTS-IN-+))
                         (12 12 (:REWRITE DEFAULT-*-1)))
(RTL::RC-CARRY)
(RTL::BVECP-1-RC-CARRY (24 12 (:REWRITE RTL::BVECP-BITN-0))
                       (16 16 (:REWRITE DEFAULT-+-2))
                       (16 16 (:REWRITE DEFAULT-+-1))
                       (12 12 (:REWRITE RTL::NEG-BITN-1))
                       (12 12 (:REWRITE RTL::NEG-BITN-0))
                       (12 12 (:REWRITE RTL::BITN-NEG))
                       (4 4 (:REWRITE ZP-OPEN)))
(RTL::RC-SUM)
(RTL::BVECP-RC-SUM (135 3 (:DEFINITION RTL::RC-CARRY))
                   (42 18 (:REWRITE RTL::BVECP-BITN-0))
                   (36 36 (:REWRITE DEFAULT-+-2))
                   (36 36 (:REWRITE DEFAULT-+-1))
                   (24 18 (:REWRITE RTL::BITN-NEG))
                   (18 18 (:REWRITE RTL::NEG-BITN-1))
                   (18 18 (:REWRITE RTL::NEG-BITN-0))
                   (16 7 (:REWRITE ZP-OPEN))
                   (13 1 (:DEFINITION EXPT))
                   (10 8 (:REWRITE DEFAULT-<-2))
                   (8 8 (:REWRITE DEFAULT-<-1))
                   (3 1 (:REWRITE DEFAULT-*-2))
                   (3 1 (:REWRITE COMMUTATIVITY-OF-+))
                   (1 1 (:REWRITE ZIP-OPEN))
                   (1 1 (:REWRITE DEFAULT-*-1)))
(RTL::LEMMA1
 (509 53
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (451
  451
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (451 451
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (451
     451
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (451 451
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (451 451
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (172 5 (:LINEAR EXPT-X->=-X))
 (172 5 (:LINEAR EXPT-X->-X))
 (156 6 (:REWRITE ODD-EXPT-THM))
 (128 38
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (128 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (128 5 (:LINEAR EXPT-<=-1-TWO))
 (119 38 (:REWRITE SIMPLIFY-SUMS-<))
 (107 53 (:REWRITE DEFAULT-LESS-THAN-2))
 (92 38
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (89 53 (:REWRITE DEFAULT-LESS-THAN-1))
 (66 39 (:REWRITE DEFAULT-PLUS-2))
 (60 15 (:REWRITE |(+ c (+ d x))|))
 (53 53 (:REWRITE THE-FLOOR-BELOW))
 (53 53 (:REWRITE THE-FLOOR-ABOVE))
 (53 53
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (53 53
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (39 39 (:REWRITE DEFAULT-PLUS-1))
 (38 38 (:REWRITE INTEGERP-<-CONSTANT))
 (38 38 (:REWRITE CONSTANT-<-INTEGERP))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< c (- x))|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< (/ x) (/ y))|))
 (38 38 (:REWRITE |(< (- x) c)|))
 (38 38 (:REWRITE |(< (- x) (- y))|))
 (31 4 (:REWRITE DEFAULT-TIMES-2))
 (25 25 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (19 19 (:REWRITE |arith (expt x c)|))
 (17 17 (:REWRITE |arith (expt 1/c n)|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (15 15 (:REWRITE |(+ 0 x)|))
 (14 14
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (13 4 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |arith (* c (* d x))|))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE NORMALIZE-ADDENDS))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-TWO))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE |arith (* (- x) y)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |arith (- (* c x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A)))
(RTL::LEMMA2
 (130 10
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (84 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (84 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (58
  58
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 34 (:REWRITE DEFAULT-PLUS-2))
 (56 34 (:REWRITE DEFAULT-PLUS-1))
 (38 4 (:REWRITE RTL::BITS-TAIL))
 (22 3 (:REWRITE DEFAULT-TIMES-1))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 15 (:REWRITE NORMALIZE-ADDENDS))
 (14 3 (:REWRITE DEFAULT-TIMES-2))
 (13 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 1
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (13 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (8 2 (:REWRITE RTL::NEG-BITN-1))
 (8 2 (:REWRITE RTL::NEG-BITN-0))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 2 (:REWRITE RTL::BVECP-BITN-0))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE RTL::BITN-NEG))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::LEMMA3
 (103 12
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (84
   84
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (84
  84
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (84 84
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (84 84
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (84 84
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (84 84
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (44 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (41 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (41 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (32 1 (:REWRITE RTL::LEMMA2))
 (31 13 (:REWRITE DEFAULT-PLUS-2))
 (31 13 (:REWRITE DEFAULT-PLUS-1))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (30 1 (:DEFINITION POSP))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (21 3 (:REWRITE DEFAULT-TIMES-2))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 3 (:REWRITE DEFAULT-TIMES-1))
 (10 1 (:REWRITE RTL::NEG-BITN-0))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE CONSTANT-<-INTEGERP))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< c (- x))|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 1 (:REWRITE RTL::BVECP-BITN-0))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE RTL::NEG-BITN-1))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::RIPPLE-CARRY
 (3710 50 (:REWRITE RTL::NEG-BITN-0))
 (2177 179
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1886 10 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1144 1144
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (865 310 (:REWRITE DEFAULT-PLUS-2))
 (607
  607
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (607 607
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (607
     607
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (607 607
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (607 607
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (600 14 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (542 310 (:REWRITE DEFAULT-PLUS-1))
 (532 532
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (532 532
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (532 532
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (532 14 (:LINEAR EXPT-X->=-X))
 (532 14 (:LINEAR EXPT-X->-X))
 (506 14 (:LINEAR EXPT-<=-1-TWO))
 (398 50 (:REWRITE RTL::NEG-BITN-1))
 (327 179 (:REWRITE DEFAULT-LESS-THAN-2))
 (318 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (318 9
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (318 9
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (270 12 (:REWRITE RTL::BITS-TAIL-GEN))
 (268 112
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (268 112
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (256 256 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (252 12 (:REWRITE RTL::BITS-NEG-INDICES))
 (242 28 (:LINEAR RTL::LOGAND-BND))
 (220 112 (:REWRITE SIMPLIFY-SUMS-<))
 (203 22 (:REWRITE DEFAULT-TIMES-1))
 (200 22 (:REWRITE DEFAULT-LOGIOR-2))
 (196 14 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (193 22 (:REWRITE DEFAULT-TIMES-2))
 (192 14 (:LINEAR EXPT->=-1-ONE))
 (187 179 (:REWRITE DEFAULT-LESS-THAN-1))
 (182 182 (:REWRITE THE-FLOOR-BELOW))
 (182 182 (:REWRITE THE-FLOOR-ABOVE))
 (179 179
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (179 179
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (166 10 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (155 155
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (155 155 (:REWRITE NORMALIZE-ADDENDS))
 (120 12 (:REWRITE DEFAULT-MINUS))
 (120 12 (:REWRITE RTL::BITS-TAIL))
 (113 113
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (113 113 (:REWRITE INTEGERP-<-CONSTANT))
 (113 113 (:REWRITE CONSTANT-<-INTEGERP))
 (113 113
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (113 113
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (113 113
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (113 113
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (113 113 (:REWRITE |(< c (- x))|))
 (113 113
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (113 113
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (113 113
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (113 113
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (113 113 (:REWRITE |(< (/ x) (/ y))|))
 (113 113 (:REWRITE |(< (- x) c)|))
 (113 113 (:REWRITE |(< (- x) (- y))|))
 (110 110
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (110 22 (:REWRITE DEFAULT-LOGIOR-1))
 (77 77 (:REWRITE |arith (expt x c)|))
 (76 38 (:REWRITE DEFAULT-LOGAND-2))
 (76 38 (:REWRITE DEFAULT-LOGAND-1))
 (74 50 (:REWRITE RTL::BVECP-BITN-0))
 (73 73 (:REWRITE |arith (expt 1/c n)|))
 (68 68 (:REWRITE |arith (* c (* d x))|))
 (66 66 (:REWRITE |(+ 0 x)|))
 (56 14 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (56 14 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (50 50 (:REWRITE RTL::BITN-NEG))
 (48 48 (:REWRITE |(< x (+ c/d y))|))
 (39 39 (:REWRITE DEFAULT-EXPT-2))
 (39 39 (:REWRITE DEFAULT-EXPT-1))
 (39 39 (:REWRITE |(expt 1/c n)|))
 (39 39 (:REWRITE |(expt (- x) n)|))
 (39 39 (:REWRITE |(< (* x y) 0)|))
 (38 38 (:REWRITE LOGAND-CONSTANT-MASK))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (36 36 (:REWRITE |arith (* (- x) y)|))
 (34 34 (:REWRITE |(< 0 (* x y))|))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 12 (:REWRITE DEFAULT-LOGXOR-2))
 (24 12 (:REWRITE DEFAULT-LOGXOR-1))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (20 20 (:REWRITE |arith (- (* c x))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-TWO))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(logior c d x)|))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE |arith (+ c (+ d x))|))
 (3 3 (:REWRITE ZP-OPEN)))
(RTL::GEN (7 7 (:REWRITE DEFAULT-<-2))
          (7 7 (:REWRITE DEFAULT-<-1))
          (6 2 (:REWRITE RTL::BVECP-BITN-0))
          (5 4 (:REWRITE DEFAULT-+-2))
          (4 4 (:REWRITE DEFAULT-+-1))
          (2 2 (:REWRITE RTL::NEG-BITN-1))
          (2 2 (:REWRITE RTL::NEG-BITN-0))
          (2 2 (:REWRITE RTL::BITN-NEG))
          (1 1
             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(RTL::PROP (7 7 (:REWRITE DEFAULT-<-2))
           (7 7 (:REWRITE DEFAULT-<-1))
           (6 2 (:REWRITE RTL::BVECP-BITN-0))
           (5 4 (:REWRITE DEFAULT-+-2))
           (4 4 (:REWRITE DEFAULT-+-1))
           (2 2 (:REWRITE RTL::NEG-BITN-1))
           (2 2 (:REWRITE RTL::NEG-BITN-0))
           (2 2 (:REWRITE RTL::BITN-NEG))
           (1 1
              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(RTL::BVECP-1-GEN (43 15 (:REWRITE RTL::BVECP-BITN-0))
                  (22 22 (:REWRITE DEFAULT-<-2))
                  (22 22 (:REWRITE DEFAULT-<-1))
                  (15 15 (:REWRITE RTL::NEG-BITN-1))
                  (15 15 (:REWRITE RTL::NEG-BITN-0))
                  (15 15 (:REWRITE RTL::BITN-NEG))
                  (2 2 (:REWRITE DEFAULT-+-2))
                  (2 2 (:REWRITE DEFAULT-+-1)))
(RTL::BVECP-1-PROP (36 12 (:REWRITE RTL::BVECP-BITN-0))
                   (22 22 (:REWRITE DEFAULT-<-2))
                   (22 22 (:REWRITE DEFAULT-<-1))
                   (12 12 (:REWRITE RTL::NEG-BITN-1))
                   (12 12 (:REWRITE RTL::NEG-BITN-0))
                   (12 12 (:REWRITE RTL::BITN-NEG))
                   (2 2 (:REWRITE DEFAULT-+-2))
                   (2 2 (:REWRITE DEFAULT-+-1)))
(RTL::GEN-VAL
 (12739 939
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10586 634
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3962
  3962
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3962
      3962
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3962
     3962
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3962 3962
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3962 3962
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3672 250 (:REWRITE |(< (+ (- c) x) y)|))
 (3180 32 (:LINEAR EXPT-<=-1-TWO))
 (3118 32 (:LINEAR EXPT-<-1-TWO))
 (2852 32 (:LINEAR EXPT-X->=-X))
 (2852 32 (:LINEAR EXPT-X->-X))
 (2828 182 (:REWRITE RTL::BITS-NEG-INDICES))
 (2690 2323 (:REWRITE DEFAULT-PLUS-2))
 (1425 946 (:REWRITE DEFAULT-LESS-THAN-2))
 (1090 634
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (946 946 (:REWRITE THE-FLOOR-BELOW))
 (946 946 (:REWRITE THE-FLOOR-ABOVE))
 (939 939
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (939 939
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (888 463 (:REWRITE SIMPLIFY-SUMS-<))
 (835 277 (:REWRITE |(< y (+ (- c) x))|))
 (701 647 (:REWRITE |(< c (- x))|))
 (695 645
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (664 664
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (647 647
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (647 647
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (647 647
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (647 647
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (647 647
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (647 647
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (647 647
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (647 647
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (647 647 (:REWRITE |(< (/ x) (/ y))|))
 (647 647 (:REWRITE |(< (- x) (- y))|))
 (645 645 (:REWRITE INTEGERP-<-CONSTANT))
 (645 645 (:REWRITE CONSTANT-<-INTEGERP))
 (645 645 (:REWRITE |(< (- x) c)|))
 (476 113
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (476 113
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (419 113 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (391 100 (:REWRITE RTL::NEG-BITN-1))
 (391 100 (:REWRITE RTL::NEG-BITN-0))
 (358 358 (:REWRITE |(< x (+ c/d y))|))
 (334 334 (:REWRITE |(< (+ c/d x) y)|))
 (294 100 (:REWRITE RTL::BVECP-BITN-0))
 (281 281 (:REWRITE INTEGERP-MINUS-X))
 (277 277 (:META META-INTEGERP-CORRECT))
 (250 25
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (250 25
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (175 175 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (164 164 (:REWRITE FOLD-CONSTS-IN-+))
 (163 163 (:REWRITE |(< (* x y) 0)|))
 (140 140 (:REWRITE DEFAULT-EXPT-1))
 (138 138 (:REWRITE |(expt 1/c n)|))
 (138 138 (:REWRITE |(expt (- x) n)|))
 (127 127 (:REWRITE |(< 0 (* x y))|))
 (117 117 (:REWRITE DEFAULT-MINUS))
 (113 113
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (113 113
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (113 113
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (113 113 (:REWRITE |(equal c (/ x))|))
 (113 113 (:REWRITE |(equal c (- x))|))
 (113 113 (:REWRITE |(equal (/ x) c)|))
 (113 113 (:REWRITE |(equal (/ x) (/ y))|))
 (113 113 (:REWRITE |(equal (- x) c)|))
 (113 113 (:REWRITE |(equal (- x) (- y))|))
 (100 100 (:REWRITE RTL::BITN-NEG))
 (100 10 (:REWRITE DEFAULT-TIMES-2))
 (88 88 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (82 82 (:REWRITE |(< 0 (/ x))|))
 (80 8
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (80 8
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (79 79 (:REWRITE |(< (/ x) 0)|))
 (72 72 (:REWRITE |arith (expt x c)|))
 (67 67
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (67 67
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (64 64
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (42 18 (:REWRITE RATIONALP-X))
 (42 6 (:REWRITE ACL2-NUMBERP-X))
 (40 40 (:REWRITE |arith (expt 1/c n)|))
 (32 32
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (32 32 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (32 32 (:LINEAR EXPT-LINEAR-UPPER-<))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<))
 (32 32 (:LINEAR EXPT->=-1-TWO))
 (32 32 (:LINEAR EXPT->-1-TWO))
 (32 32 (:LINEAR EXPT-<=-1-ONE))
 (32 32 (:LINEAR EXPT-<-1-ONE))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (25 25
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (22 22 (:REWRITE |(equal (+ (- c) x) y)|))
 (18 18 (:REWRITE REDUCE-RATIONALP-+))
 (18 18 (:REWRITE REDUCE-RATIONALP-*))
 (18 18 (:REWRITE RATIONALP-MINUS-X))
 (18 18 (:META META-RATIONALP-CORRECT))
 (14 10 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:REWRITE |arith (+ c (+ d x))|))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE |(- (- x))|)))
(RTL::LEMMA
 (2542
  2542
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2542
      2542
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2542
     2542
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2542 2542
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2542 2542
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1584 1134
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1392 223 (:REWRITE DEFAULT-TIMES-1))
 (1332 223 (:REWRITE DEFAULT-TIMES-2))
 (1288 28 (:REWRITE |(* (* x y) z)|))
 (1134 1134
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (1134 1134
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1097 5 (:REWRITE FLOOR-ZERO . 3))
 (1052 9 (:REWRITE FLOOR-ZERO . 5))
 (971 5 (:REWRITE CANCEL-FLOOR-+))
 (875 9 (:REWRITE FLOOR-=-X/Y . 3))
 (867 9 (:REWRITE FLOOR-=-X/Y . 2))
 (837 164
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (809 9 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (736 191 (:REWRITE DEFAULT-LESS-THAN-1))
 (681 164
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (640 188 (:REWRITE |(< c (- x))|))
 (638 195 (:REWRITE DEFAULT-LESS-THAN-2))
 (616 8 (:REWRITE |(* (- x) y)|))
 (579 9 (:REWRITE DEFAULT-FLOOR-RATIO))
 (527 17 (:REWRITE ODD-EXPT-THM))
 (517 13 (:LINEAR EXPT->=-1-ONE))
 (512 13 (:LINEAR EXPT-<=-1-TWO))
 (504 13 (:LINEAR EXPT-<-1-TWO))
 (499 13 (:LINEAR EXPT->-1-ONE))
 (472 5 (:REWRITE DEFAULT-MOD-RATIO))
 (460 188
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (439 13 (:LINEAR EXPT-X->=-X))
 (439 13 (:LINEAR EXPT-X->-X))
 (416 172 (:REWRITE |(< (- x) c)|))
 (390 4 (:REWRITE MOD-X-Y-=-X . 4))
 (386 164
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (372 4 (:REWRITE MOD-ZERO . 3))
 (350 2 (:REWRITE CANCEL-MOD-+))
 (344 8 (:REWRITE |(integerp (- x))|))
 (322 4 (:REWRITE MOD-ZERO . 4))
 (317 164 (:REWRITE SIMPLIFY-SUMS-<))
 (312 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (261 9 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (255 5 (:REWRITE |(floor x 1)|))
 (202 98 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (195 195 (:REWRITE THE-FLOOR-BELOW))
 (195 195 (:REWRITE THE-FLOOR-ABOVE))
 (190 19 (:REWRITE DEFAULT-DIVIDE))
 (188 188
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (188 188
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (188 188
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (188 188
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (188 188
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (188 188
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (188 188
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (188 188
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (188 188
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (188 188
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (188 188 (:REWRITE |(< (/ x) (/ y))|))
 (188 188 (:REWRITE |(< (- x) (- y))|))
 (183 9 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (183 9 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (169 65 (:REWRITE DEFAULT-MINUS))
 (164 164 (:REWRITE INTEGERP-<-CONSTANT))
 (164 164 (:REWRITE CONSTANT-<-INTEGERP))
 (160 72 (:REWRITE REDUCE-INTEGERP-+))
 (126 24 (:REWRITE DEFAULT-PLUS-1))
 (120 24 (:REWRITE DEFAULT-PLUS-2))
 (109 5 (:REWRITE DEFAULT-MOD-1))
 (108 12 (:REWRITE ACL2-NUMBERP-X))
 (104 56
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (104 56
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (104 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (87 9 (:REWRITE DEFAULT-FLOOR-1))
 (86 2 (:REWRITE RTL::FL+INT-REWRITE))
 (86 2 (:REWRITE |(mod x 1)|))
 (83 5 (:REWRITE FLOOR-ZERO . 2))
 (83 5
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (83 5 (:REWRITE FLOOR-CANCEL-*-CONST))
 (83 1 (:REWRITE RTL::INTEGERP-FL))
 (79 1 (:REWRITE |(* (if a b c) x)|))
 (78 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (78 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (72 72 (:REWRITE INTEGERP-MINUS-X))
 (72 72 (:META META-INTEGERP-CORRECT))
 (66 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (64 64 (:REWRITE |(< 0 (/ x))|))
 (64 64 (:REWRITE |(< 0 (* x y))|))
 (54 2 (:REWRITE MOD-X-Y-=-X . 2))
 (54 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (54 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (48 12 (:REWRITE RATIONALP-X))
 (47 47 (:REWRITE |(< (/ x) 0)|))
 (47 47 (:REWRITE |(< (* x y) 0)|))
 (45 45 (:REWRITE |arith (expt x c)|))
 (45 45 (:REWRITE |arith (expt 1/c n)|))
 (45 9 (:REWRITE DEFAULT-FLOOR-2))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (44 44
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (44 44
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (44 44 (:REWRITE DEFAULT-EXPT-1))
 (44 44 (:REWRITE |(expt 1/c n)|))
 (44 44 (:REWRITE |(expt (- x) n)|))
 (43 1 (:REWRITE |(floor (+ x r) i)|))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (34 2 (:REWRITE RTL::NEG-BITN-0))
 (31 1 (:DEFINITION NATP))
 (30 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (30 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (30 1 (:REWRITE RTL::BITN-NEG))
 (28 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (28 2 (:REWRITE MOD-CANCEL-*-CONST))
 (26 26
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 24 (:REWRITE |(- (- x))|))
 (23 5 (:REWRITE DEFAULT-MOD-2))
 (15 15 (:REWRITE |arith (* c (* d x))|))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (13 13 (:LINEAR EXPT->=-1-TWO))
 (13 13 (:LINEAR EXPT->-1-TWO))
 (13 13 (:LINEAR EXPT-<=-1-ONE))
 (13 13 (:LINEAR EXPT-<-1-ONE))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE |arith (- (* c x))|))
 (6 6 (:REWRITE |arith (* (- x) y)|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (5 5
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5 (:REWRITE |(floor x (- y))| . 2))
 (5 5 (:REWRITE |(floor x (- y))| . 1))
 (5 5
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (5 5
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(floor (- x) y)| . 2))
 (5 5 (:REWRITE |(floor (- x) y)| . 1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE RTL::NEG-BITN-1))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::GEN-VAL-COR1 (58 2 (:DEFINITION EXPT))
                   (24 12 (:REWRITE FOLD-CONSTS-IN-+))
                   (24 4 (:REWRITE COMMUTATIVITY-OF-+))
                   (23 19 (:REWRITE DEFAULT-+-1))
                   (22 19 (:REWRITE DEFAULT-+-2))
                   (14 6 (:REWRITE DEFAULT-*-2))
                   (12 7 (:REWRITE DEFAULT-<-1))
                   (11 7 (:REWRITE DEFAULT-<-2))
                   (7 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
                   (6 6 (:REWRITE DEFAULT-*-1))
                   (6 4 (:REWRITE RTL::BITS-NEG-INDICES))
                   (4 2 (:REWRITE ZIP-OPEN))
                   (4 2 (:REWRITE UNICITY-OF-0))
                   (2 2
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                   (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                   (2 2 (:DEFINITION FIX)))
(RTL::GEN-VAL-COR2
 (4410 10 (:REWRITE RTL::MOD-DOES-NOTHING))
 (3072 192 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3072 192
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (3072 192
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2819 195
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2616 41 (:REWRITE DEFAULT-MOD-RATIO))
 (1736
  1736
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1736
      1736
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1736
     1736
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1736 1736
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1736 1736
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1736 1736
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1624 236 (:REWRITE DEFAULT-TIMES-2))
 (1572 11 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1538 11 (:REWRITE CANCEL-MOD-+))
 (1484 220 (:REWRITE DEFAULT-LESS-THAN-1))
 (1344 192 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1081 11 (:REWRITE MOD-ZERO . 3))
 (942 942
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (942 942
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (942 942
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (942 942
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (790 79 (:REWRITE DEFAULT-DIVIDE))
 (618 127 (:REWRITE SIMPLIFY-SUMS-<))
 (618 127
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (596 11 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (588 49 (:REWRITE |(/ (expt x n))|))
 (549 23 (:REWRITE ODD-EXPT-THM))
 (546 127
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (521 21 (:LINEAR EXPT-X->=-X))
 (521 21 (:LINEAR EXPT-X->-X))
 (510 30 (:REWRITE |(/ (if a b c))|))
 (508 11 (:REWRITE MOD-X-Y-=-X . 4))
 (508 11 (:REWRITE MOD-X-Y-=-X . 3))
 (501 21 (:LINEAR EXPT->=-1-ONE))
 (501 21 (:LINEAR EXPT-<=-1-TWO))
 (491 21 (:LINEAR EXPT->-1-ONE))
 (491 21 (:LINEAR EXPT-<-1-TWO))
 (481 220 (:REWRITE DEFAULT-LESS-THAN-2))
 (452 236 (:REWRITE DEFAULT-TIMES-1))
 (374 11 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (374 11
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (372 12 (:REWRITE |(integerp (- x))|))
 (320 11 (:REWRITE MOD-ZERO . 4))
 (294 49 (:REWRITE |(- (+ x y))|))
 (288 12 (:REWRITE |(* (- x) y)|))
 (275 41 (:REWRITE DEFAULT-MOD-2))
 (275 11 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (275 11 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (275 11 (:REWRITE MOD-X-Y-=-X . 2))
 (274 70 (:REWRITE |(+ c (+ d x))|))
 (228 111 (:REWRITE DEFAULT-MINUS))
 (220 220 (:REWRITE THE-FLOOR-BELOW))
 (220 220 (:REWRITE THE-FLOOR-ABOVE))
 (195 195
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (195 195
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (192 192 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (192 192
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (192 192
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (192 192
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (176 11
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (176 11
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (176 11
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (163 163
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (163 163
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (163 163
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (163 163
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (148 148
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (147 28 (:REWRITE ACL2-NUMBERP-X))
 (127 127
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (127 127 (:REWRITE INTEGERP-<-CONSTANT))
 (127 127 (:REWRITE CONSTANT-<-INTEGERP))
 (127 127
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (127 127
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (127 127
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (127 127
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (127 127 (:REWRITE |(< c (- x))|))
 (127 127
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (127 127
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (127 127
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (127 127
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (127 127 (:REWRITE |(< (/ x) (/ y))|))
 (127 127 (:REWRITE |(< (- x) c)|))
 (127 127 (:REWRITE |(< (- x) (- y))|))
 (116 11 (:REWRITE MOD-CANCEL-*-CONST))
 (94 94 (:REWRITE REDUCE-INTEGERP-+))
 (94 94 (:REWRITE INTEGERP-MINUS-X))
 (94 94 (:META META-INTEGERP-CORRECT))
 (91 91
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (65 65 (:REWRITE DEFAULT-EXPT-1))
 (64 64 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (59 59 (:REWRITE |(< 0 (* x y))|))
 (56 56 (:REWRITE |(expt 1/c n)|))
 (56 56 (:REWRITE |(expt (- x) n)|))
 (56 5 (:REWRITE RTL::BITS-TAIL))
 (56 5 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (55 16 (:REWRITE RATIONALP-X))
 (49 49 (:REWRITE |(< x (+ c/d y))|))
 (48 5 (:REWRITE RTL::BITS-NEG-INDICES))
 (45 45 (:REWRITE |(< (* x y) 0)|))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (42 42
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (42 42
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (41 41 (:REWRITE DEFAULT-MOD-1))
 (40 5 (:REWRITE RTL::BITS-TAIL-GEN))
 (34 1 (:DEFINITION NATP))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (31 31 (:REWRITE |(< 0 (/ x))|))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 25 (:REWRITE |(< (/ x) 0)|))
 (25 25 (:REWRITE |(< (+ c/d x) y)|))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<))
 (21 21 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (21 21 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 21 (:LINEAR EXPT->=-1-TWO))
 (21 21 (:LINEAR EXPT->-1-TWO))
 (21 21 (:LINEAR EXPT-<=-1-ONE))
 (21 21 (:LINEAR EXPT-<-1-ONE))
 (19 1 (:REWRITE SUM-IS-EVEN . 2))
 (16 16 (:REWRITE REDUCE-RATIONALP-+))
 (16 16 (:REWRITE REDUCE-RATIONALP-*))
 (16 16 (:REWRITE RATIONALP-MINUS-X))
 (16 16 (:META META-RATIONALP-CORRECT))
 (12 12 (:REWRITE |(- (* c x))|))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (11 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11 11
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (11 11
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11 11 (:REWRITE |(mod x (- y))| . 3))
 (11 11 (:REWRITE |(mod x (- y))| . 2))
 (11 11 (:REWRITE |(mod x (- y))| . 1))
 (11 11
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (11 11 (:REWRITE |(mod (- x) y)| . 3))
 (11 11 (:REWRITE |(mod (- x) y)| . 2))
 (11 11 (:REWRITE |(mod (- x) y)| . 1))
 (11 11
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (11 11 (:REWRITE |(equal c (/ x))|))
 (11 11 (:REWRITE |(equal c (- x))|))
 (11 11 (:REWRITE |(equal (/ x) c)|))
 (11 11 (:REWRITE |(equal (/ x) (/ y))|))
 (11 11 (:REWRITE |(equal (- x) c)|))
 (11 11 (:REWRITE |(equal (- x) (- y))|))
 (10 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5 5 (:REWRITE |(mod x 2)| . 2))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|)))
(RTL::GEN-SPECIAL-CASE
 (11249 921
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4253 168 (:REWRITE RTL::BITS-NEG-INDICES))
 (3851 38 (:REWRITE ODD-EXPT-THM))
 (3383
  3383
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3383
      3383
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3383
     3383
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3383 3383
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3383 3383
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3072 215 (:REWRITE |(< (+ (- c) x) y)|))
 (3016 2529 (:REWRITE DEFAULT-PLUS-1))
 (2833 27 (:LINEAR EXPT-<=-1-TWO))
 (2779 27 (:LINEAR EXPT-<-1-TWO))
 (2719 2529 (:REWRITE DEFAULT-PLUS-2))
 (2534 27 (:LINEAR EXPT-X->=-X))
 (2534 27 (:LINEAR EXPT-X->-X))
 (2368 168
       (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1803 63 (:REWRITE RTL::BITN-NEG))
 (1265 921 (:REWRITE DEFAULT-LESS-THAN-2))
 (1208 669
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (972 921 (:REWRITE DEFAULT-LESS-THAN-1))
 (921 921 (:REWRITE THE-FLOOR-BELOW))
 (921 921 (:REWRITE THE-FLOOR-ABOVE))
 (921 921
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (921 921
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (853 671
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (796 269 (:REWRITE |(< y (+ (- c) x))|))
 (671 671 (:REWRITE INTEGERP-<-CONSTANT))
 (671 671 (:REWRITE CONSTANT-<-INTEGERP))
 (671 671
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (671 671
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (671 671
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (671 671
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (671 671 (:REWRITE |(< c (- x))|))
 (671 671
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (671 671
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (671 671
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (671 671
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (671 671 (:REWRITE |(< (/ x) (/ y))|))
 (671 671 (:REWRITE |(< (- x) c)|))
 (671 671 (:REWRITE |(< (- x) (- y))|))
 (567 567
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (462 20 (:REWRITE DEFAULT-LOGXOR-2))
 (412 75 (:REWRITE RTL::NEG-BITN-0))
 (401 89
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (399 89
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (354 89 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (339 339 (:REWRITE |(< x (+ c/d y))|))
 (287 287 (:REWRITE |(< (+ c/d x) y)|))
 (280 75 (:REWRITE RTL::NEG-BITN-1))
 (264 264 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (226 226 (:REWRITE |(< (* x y) 0)|))
 (210 42 (:REWRITE DEFAULT-TIMES-2))
 (179 95 (:REWRITE |(equal (/ x) c)|))
 (173 173 (:REWRITE REDUCE-INTEGERP-+))
 (173 173 (:REWRITE INTEGERP-MINUS-X))
 (173 173 (:META META-INTEGERP-CORRECT))
 (167 167
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (167 167
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (154 154 (:REWRITE |(< (/ x) 0)|))
 (144 144
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (144 144
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (134 134 (:REWRITE FOLD-CONSTS-IN-+))
 (130 13
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (130 13
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (111 111 (:REWRITE |(< 0 (* x y))|))
 (105 105 (:REWRITE DEFAULT-EXPT-2))
 (105 105 (:REWRITE DEFAULT-EXPT-1))
 (105 105 (:REWRITE |(expt 1/c n)|))
 (105 105 (:REWRITE |(expt (- x) n)|))
 (99 99 (:REWRITE DEFAULT-MINUS))
 (95 95
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (95 95
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (95 95 (:REWRITE |(equal c (/ x))|))
 (95 95 (:REWRITE |(equal (/ x) (/ y))|))
 (95 95 (:REWRITE |(equal (- x) (- y))|))
 (89 89
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (89 89 (:REWRITE |(equal c (- x))|))
 (89 89 (:REWRITE |(equal (- x) c)|))
 (78 2 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (75 75 (:REWRITE |(< 0 (/ x))|))
 (68 68
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (68 68
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (54 54
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (54 54
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (54 54
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (54 54
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (52 42 (:REWRITE DEFAULT-TIMES-1))
 (40 40 (:REWRITE |arith (expt x c)|))
 (40 40 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (40 4
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (40 4
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (27 27 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (27 27 (:LINEAR EXPT-LINEAR-UPPER-<))
 (27 27 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (27 27 (:LINEAR EXPT-LINEAR-LOWER-<))
 (27 27 (:LINEAR EXPT->=-1-TWO))
 (27 27 (:LINEAR EXPT->-1-TWO))
 (27 27 (:LINEAR EXPT-<=-1-ONE))
 (27 27 (:LINEAR EXPT-<-1-ONE))
 (24 24 (:REWRITE |arith (expt 1/c n)|))
 (24 24 (:REWRITE |(equal (+ (- c) x) y)|))
 (24 20 (:REWRITE DEFAULT-LOGXOR-1))
 (20 10 (:REWRITE DEFAULT-LOGIOR-2))
 (16 16
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (14 10 (:REWRITE DEFAULT-LOGIOR-1))
 (13 13
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (13 13
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:REWRITE |(* (- x) y)|))
 (8 2 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (6 6 (:REWRITE |(not (equal x (/ y)))|))
 (6 6 (:REWRITE |(equal x (/ y))|))
 (6 6 (:REWRITE |(/ (/ x))|))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (4 4 (:REWRITE |arith (+ c (+ d x))|))
 (4 4 (:REWRITE |arith (* c (* d x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 5))
 (1 1
    (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 4))
 (1 1
    (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 3))
 (1 1
    (:REWRITE |(integerp (* 1/2 (logxor x y)))| . 2))
 (1 1 (:REWRITE |(equal x (if a b c))|)))
(RTL::LEMMA0
 (4493 1 (:REWRITE DEFAULT-MOD-RATIO))
 (2300 230
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1891
  1891
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1891
      1891
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1891
     1891
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1891 1891
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1668 7 (:REWRITE FLOOR-ZERO . 3))
 (1564 34 (:REWRITE |(* (* x y) z)|))
 (1333 218 (:REWRITE DEFAULT-TIMES-1))
 (1326 218 (:REWRITE DEFAULT-TIMES-2))
 (1046 7 (:REWRITE CANCEL-FLOOR-+))
 (928 12 (:REWRITE FLOOR-=-X/Y . 2))
 (844 12 (:REWRITE DEFAULT-FLOOR-RATIO))
 (604 86
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (587 7 (:REWRITE |(* (- x) y)|))
 (521 68
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (521 68 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (508 12 (:REWRITE FLOOR-=-X/Y . 3))
 (467 86 (:REWRITE DEFAULT-LESS-THAN-1))
 (356 12 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (301 11 (:REWRITE FLOOR-ZERO . 5))
 (254 12 (:LINEAR EXPT-X->=-X))
 (254 12 (:LINEAR EXPT-X->-X))
 (232 12 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (232 12 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (230 230
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (230 230
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (216 8 (:REWRITE |(floor x 1)|))
 (215 9 (:REWRITE ODD-EXPT-THM))
 (176 68 (:REWRITE SIMPLIFY-SUMS-<))
 (167 86 (:REWRITE DEFAULT-LESS-THAN-2))
 (140 68
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (139 24 (:REWRITE DEFAULT-MINUS))
 (137 1 (:REWRITE RTL::BVECP-BITN-0))
 (136 12 (:REWRITE DEFAULT-FLOOR-1))
 (122 7 (:REWRITE FLOOR-ZERO . 2))
 (122 7
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (122 7 (:REWRITE FLOOR-CANCEL-*-CONST))
 (118 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (118 2
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (118 2
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (115 115 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (115 115 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (115 115 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (115 115
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (110 110
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (110 110
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (110 110
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (106 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (93 3 (:REWRITE |(integerp (- x))|))
 (90 9 (:REWRITE DEFAULT-DIVIDE))
 (89 89 (:REWRITE |arith (expt x c)|))
 (86 86 (:REWRITE THE-FLOOR-BELOW))
 (86 86 (:REWRITE THE-FLOOR-ABOVE))
 (86 86
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (86 86
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (85 85 (:REWRITE |arith (expt 1/c n)|))
 (84 75 (:REWRITE DEFAULT-PLUS-2))
 (79 75 (:REWRITE DEFAULT-PLUS-1))
 (68 68 (:REWRITE INTEGERP-<-CONSTANT))
 (68 68 (:REWRITE CONSTANT-<-INTEGERP))
 (68 68
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (68 68
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (68 68
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (68 68
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (68 68 (:REWRITE |(< c (- x))|))
 (68 68
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (68 68
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (68 68
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (68 68
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (68 68 (:REWRITE |(< (/ x) (/ y))|))
 (68 68 (:REWRITE |(< (- x) c)|))
 (68 68 (:REWRITE |(< (- x) (- y))|))
 (64 10
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (64 10
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (52 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 12 (:REWRITE DEFAULT-FLOOR-2))
 (46 10
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (46 10
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (44 44 (:REWRITE DEFAULT-EXPT-2))
 (44 44 (:REWRITE DEFAULT-EXPT-1))
 (44 44 (:REWRITE |(expt 1/c n)|))
 (44 44 (:REWRITE |(expt (- x) n)|))
 (31 1 (:REWRITE RTL::INTEGERP-FL))
 (30 30 (:REWRITE REDUCE-INTEGERP-+))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (30 30 (:META META-INTEGERP-CORRECT))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (28 28
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (28 28
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (28 28
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (25 1 (:REWRITE DEFAULT-MOD-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE |arith (* c (* d x))|))
 (15 15 (:REWRITE |(< 0 (* x y))|))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (10 1 (:REWRITE RTL::NEG-BITN-0))
 (7 7
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (7 7 (:REWRITE |(floor x (- y))| . 2))
 (7 7 (:REWRITE |(floor x (- y))| . 1))
 (7 7
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (7 7
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (7 7 (:REWRITE |(floor (- x) y)| . 2))
 (7 7 (:REWRITE |(floor (- x) y)| . 1))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE |arith (* (- x) y)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (4 4 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (4 4 (:REWRITE |(* 1/2 (floor x y))| . 2))
 (3 3
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |arith (- (* c x))|))
 (2 2 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE RTL::NEG-BITN-1))
 (1 1 (:REWRITE DEFAULT-MOD-2))
 (1 1 (:REWRITE RTL::BITN-NEG))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(RTL::LEMMA
 (3072
  3072
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3072
      3072
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3072
     3072
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3072 3072
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3072 3072
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1943 206
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (731 34 (:REWRITE ODD-EXPT-THM))
 (660 20 (:LINEAR EXPT-X->=-X))
 (660 20 (:LINEAR EXPT-X->-X))
 (541 145 (:REWRITE SIMPLIFY-SUMS-<))
 (541 145
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (541 145
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (512 206 (:REWRITE DEFAULT-LESS-THAN-2))
 (430 20 (:LINEAR EXPT-<=-1-TWO))
 (388 145
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (332 206 (:REWRITE DEFAULT-LESS-THAN-1))
 (302 86 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (274 175 (:REWRITE DEFAULT-PLUS-2))
 (228 57 (:REWRITE |(+ c (+ d x))|))
 (206 206 (:REWRITE THE-FLOOR-BELOW))
 (206 206 (:REWRITE THE-FLOOR-ABOVE))
 (206 206
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (206 206
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (175 175 (:REWRITE DEFAULT-PLUS-1))
 (145 145 (:REWRITE INTEGERP-<-CONSTANT))
 (145 145 (:REWRITE CONSTANT-<-INTEGERP))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< c (- x))|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< (/ x) (/ y))|))
 (145 145 (:REWRITE |(< (- x) c)|))
 (145 145 (:REWRITE |(< (- x) (- y))|))
 (130 13 (:REWRITE RTL::NEG-BITN-0))
 (105 105 (:REWRITE DEFAULT-EXPT-2))
 (105 105 (:REWRITE DEFAULT-EXPT-1))
 (105 105 (:REWRITE |(expt 1/c n)|))
 (105 105 (:REWRITE |(expt (- x) n)|))
 (88 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (88 16
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (79 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (67 67 (:REWRITE |(< x (+ c/d y))|))
 (61 61
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (61 61 (:REWRITE NORMALIZE-ADDENDS))
 (57 57 (:REWRITE |(+ 0 x)|))
 (44 44 (:REWRITE |(< 0 (* x y))|))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:REWRITE INTEGERP-MINUS-X))
 (23 23 (:META META-INTEGERP-CORRECT))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<))
 (20 20 (:LINEAR EXPT-LINEAR-LOWER-<))
 (20 20 (:LINEAR EXPT->=-1-TWO))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT-<=-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-TWO))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (18 18 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (17 17 (:REWRITE |(< (/ x) 0)|))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (16 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (16 16
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (16 16
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (16 16 (:REWRITE |(equal c (/ x))|))
 (16 16 (:REWRITE |(equal c (- x))|))
 (16 16 (:REWRITE |(equal (/ x) c)|))
 (16 16 (:REWRITE |(equal (/ x) (/ y))|))
 (16 16 (:REWRITE |(equal (- x) c)|))
 (16 16 (:REWRITE |(equal (- x) (- y))|))
 (14 14 (:REWRITE |arith (expt x c)|))
 (13 13 (:REWRITE RTL::NEG-BITN-1))
 (10 10 (:REWRITE |arith (expt 1/c n)|))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE RTL::BITN-NEG))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::PROP-VAL (932 772 (:REWRITE DEFAULT-+-2))
               (857 772 (:REWRITE DEFAULT-+-1))
               (831 182 (:REWRITE RTL::BVECP-BITN-0))
               (557 216 (:REWRITE DEFAULT-*-2))
               (305 305 (:REWRITE DEFAULT-<-2))
               (305 305 (:REWRITE DEFAULT-<-1))
               (232 182 (:REWRITE RTL::NEG-BITN-1))
               (220 216 (:REWRITE DEFAULT-*-1))
               (207 182 (:REWRITE RTL::NEG-BITN-0))
               (207 182 (:REWRITE RTL::BITN-NEG))
               (200 146 (:REWRITE RTL::BITS-NEG-INDICES))
               (150 30 (:REWRITE RTL::BITS-BVECP))
               (125 125 (:REWRITE DEFAULT-UNARY-MINUS)))
(RTL::PROP-AS-LOGXOR (404 16 (:DEFINITION EXPT))
                     (200 169 (:REWRITE DEFAULT-+-2))
                     (182 4 (:REWRITE RTL::BITS-TAIL-GEN))
                     (176 169 (:REWRITE DEFAULT-+-1))
                     (94 34 (:REWRITE DEFAULT-*-2))
                     (44 42 (:REWRITE RTL::BITS-REVERSE-INDICES))
                     (44 42 (:REWRITE RTL::BITS-NEG-INDICES))
                     (44 36 (:REWRITE DEFAULT-<-2))
                     (42 36 (:REWRITE DEFAULT-<-1))
                     (34 34 (:REWRITE DEFAULT-*-1))
                     (25 25 (:REWRITE DEFAULT-UNARY-MINUS))
                     (14 14 (:REWRITE ZIP-OPEN)))
(RTL::GEN-EXTEND (227 77 (:REWRITE RTL::BVECP-BITN-0))
                 (91 91 (:REWRITE DEFAULT-<-2))
                 (91 91 (:REWRITE DEFAULT-<-1))
                 (77 77 (:REWRITE RTL::NEG-BITN-1))
                 (77 77 (:REWRITE RTL::NEG-BITN-0))
                 (77 77 (:REWRITE RTL::BITN-NEG))
                 (55 55 (:REWRITE DEFAULT-+-2))
                 (55 55 (:REWRITE DEFAULT-+-1)))
(RTL::LEMMA1
 (1112
  1112
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1112
      1112
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1112
     1112
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1112 1112
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1112 1112
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (628 82
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (238 7 (:LINEAR EXPT-X->=-X))
 (238 7 (:LINEAR EXPT-X->-X))
 (185 59 (:REWRITE SIMPLIFY-SUMS-<))
 (185 59
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (185 59 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (172 82 (:REWRITE DEFAULT-LESS-THAN-1))
 (171 7 (:LINEAR EXPT-<=-1-TWO))
 (154 82 (:REWRITE DEFAULT-LESS-THAN-2))
 (131 41 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (88 6 (:REWRITE ODD-EXPT-THM))
 (87 69 (:REWRITE DEFAULT-PLUS-2))
 (82 82 (:REWRITE THE-FLOOR-BELOW))
 (82 82 (:REWRITE THE-FLOOR-ABOVE))
 (82 82
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (82 82
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (76 22 (:REWRITE |(+ c (+ d x))|))
 (69 69 (:REWRITE DEFAULT-PLUS-1))
 (62 62 (:REWRITE INTEGERP-<-CONSTANT))
 (62 62 (:REWRITE CONSTANT-<-INTEGERP))
 (62 62
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (62 62
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (62 62
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (62 62
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (62 62 (:REWRITE |(< c (- x))|))
 (62 62
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (62 62
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (62 62
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (62 62
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (62 62 (:REWRITE |(< (/ x) (/ y))|))
 (62 62 (:REWRITE |(< (- x) c)|))
 (62 62 (:REWRITE |(< (- x) (- y))|))
 (32 32 (:REWRITE DEFAULT-EXPT-2))
 (32 32 (:REWRITE DEFAULT-EXPT-1))
 (32 32 (:REWRITE |(expt 1/c n)|))
 (32 32 (:REWRITE |(expt (- x) n)|))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31 (:REWRITE NORMALIZE-ADDENDS))
 (26 26 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:REWRITE |(+ 0 x)|))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:REWRITE INTEGERP-MINUS-X))
 (16 16 (:META META-INTEGERP-CORRECT))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:LINEAR EXPT->=-1-TWO))
 (7 7 (:LINEAR EXPT->-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (5 5 (:REWRITE |arith (expt x c)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |arith (expt 1/c n)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (1 1 (:REWRITE |arith (+ c (+ d x))|)))
(RTL::LEMMA2
 (4268 1 (:REWRITE DEFAULT-MOD-RATIO))
 (1646 17 (:REWRITE |(* (* x y) z)|))
 (1326 168 (:REWRITE DEFAULT-TIMES-2))
 (1145
  1145
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1145
      1145
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1145
     1145
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1145 1145
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1145 1145
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1092 1092
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1092 1092
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1092 1092
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1092 1092
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (1092 1092
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1028 7 (:REWRITE FLOOR-=-X/Y . 3))
 (993 7 (:REWRITE FLOOR-=-X/Y . 2))
 (981 93 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (849 105
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (804 7 (:REWRITE DEFAULT-FLOOR-RATIO))
 (720 12 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (693 93
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (622 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (622 4
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (622 4
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (553 168 (:REWRITE DEFAULT-TIMES-1))
 (550 82
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (498 6 (:REWRITE FLOOR-ZERO . 5))
 (483 105
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (483 105
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (483 105
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (408 12 (:REWRITE |(* (/ c) (expt d n))|))
 (404 76
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (399 93 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (399 93
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (399 93
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (381 2 (:REWRITE FLOOR-ZERO . 3))
 (318 18 (:LINEAR EXPT-X->=-X))
 (318 18 (:LINEAR EXPT-X->-X))
 (303 76 (:REWRITE DEFAULT-LESS-THAN-2))
 (296 1 (:REWRITE RTL::BVECP-BITN-0))
 (289 2 (:REWRITE CANCEL-FLOOR-+))
 (258 60 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (238 70
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (222 222
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (222 222
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (222 222
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (210 21 (:REWRITE DEFAULT-DIVIDE))
 (209 7 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (186 60 (:REWRITE SIMPLIFY-SUMS-<))
 (180 7 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (180 7 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (174 22 (:REWRITE ODD-EXPT-THM))
 (170 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (160 76 (:REWRITE DEFAULT-LESS-THAN-1))
 (145 1 (:REWRITE DEFAULT-MOD-1))
 (140 68
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (138 18 (:LINEAR EXPT-<=-1-TWO))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (105 2 (:REWRITE |(* (- x) y)|))
 (101 101 (:REWRITE DEFAULT-EXPT-2))
 (101 101 (:REWRITE DEFAULT-EXPT-1))
 (101 101 (:REWRITE |(expt 1/c n)|))
 (101 101 (:REWRITE |(expt (- x) n)|))
 (90 9 (:REWRITE |(* c (expt d n))|))
 (88 8 (:REWRITE |(+ y (+ x z))|))
 (86 2 (:REWRITE |(integerp (- x))|))
 (84 76
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (84 76
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (76 76 (:REWRITE THE-FLOOR-BELOW))
 (76 76 (:REWRITE THE-FLOOR-ABOVE))
 (69 68 (:REWRITE DEFAULT-PLUS-1))
 (69 45
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (68 68 (:REWRITE INTEGERP-<-CONSTANT))
 (68 68 (:REWRITE DEFAULT-PLUS-2))
 (68 68 (:REWRITE CONSTANT-<-INTEGERP))
 (68 68
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (68 68
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (68 68
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (68 68
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (68 68 (:REWRITE |(< c (- x))|))
 (68 68
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (68 68
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (68 68
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (68 68
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (68 68 (:REWRITE |(< (/ x) (/ y))|))
 (68 68 (:REWRITE |(< (- x) c)|))
 (68 68 (:REWRITE |(< (- x) (- y))|))
 (62 36 (:REWRITE DEFAULT-MINUS))
 (61 7 (:REWRITE DEFAULT-FLOOR-2))
 (44 35 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (43 1 (:REWRITE RTL::INTEGERP-FL))
 (43 1 (:REWRITE |(floor x 1)|))
 (41 41
     (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
 (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (39 2 (:REWRITE FLOOR-ZERO . 2))
 (36 36
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (36 36
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (36 36
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 7 (:REWRITE DEFAULT-FLOOR-1))
 (33 33
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (32 8 (:REWRITE |(+ c (+ d x))|))
 (30 30 (:REWRITE REDUCE-INTEGERP-+))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (30 30 (:META META-INTEGERP-CORRECT))
 (30 2
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (30 2 (:REWRITE FLOOR-CANCEL-*-CONST))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (26 26 (:REWRITE |(< 0 (/ x))|))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (18 18 (:LINEAR EXPT-LINEAR-UPPER-<))
 (18 18 (:LINEAR EXPT-LINEAR-LOWER-<))
 (18 18 (:LINEAR EXPT->=-1-TWO))
 (18 18 (:LINEAR EXPT->-1-TWO))
 (18 18 (:LINEAR EXPT-<=-1-ONE))
 (18 18 (:LINEAR EXPT-<-1-TWO))
 (18 18 (:LINEAR EXPT-<-1-ONE))
 (17 2
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (12 12 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (12 12 (:REWRITE |(* c (* d x))|))
 (10 1 (:REWRITE RTL::NEG-BITN-0))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE |(+ 0 x)|))
 (5 5
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE |(floor x (- y))| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 1))
 (2 2
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor (- x) y)| . 2))
 (2 2 (:REWRITE |(floor (- x) y)| . 1))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (2 2 (:REWRITE |(* 1/2 (floor x y))| . 2))
 (1 1 (:REWRITE RTL::NEG-BITN-1))
 (1 1 (:REWRITE DEFAULT-MOD-2))
 (1 1 (:REWRITE RTL::BITN-NEG))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|)))
(RTL::LEMMA3
 (1457 82
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (994
  994
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (994 994
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (994
     994
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (994 994
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (994 994
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (990 59 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (483 7 (:REWRITE ODD-EXPT-THM))
 (470 242 (:REWRITE DEFAULT-PLUS-2))
 (415 242 (:REWRITE DEFAULT-PLUS-1))
 (331 331
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (328 8 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (238 2 (:LINEAR EXPT-<=-1-TWO))
 (234 2 (:LINEAR EXPT-<-1-TWO))
 (228 228
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (228 228
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (228 228
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (204 2 (:LINEAR EXPT-X->=-X))
 (204 2 (:LINEAR EXPT-X->-X))
 (182 59
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (179 1
      (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (166 82 (:REWRITE DEFAULT-LESS-THAN-2))
 (117 82 (:REWRITE DEFAULT-LESS-THAN-1))
 (99 19 (:REWRITE DEFAULT-LOGIOR-2))
 (89 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (89 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (87 45 (:REWRITE |(+ c (+ d x))|))
 (83 21 (:REWRITE |(< y (+ (- c) x))|))
 (82 82 (:REWRITE THE-FLOOR-BELOW))
 (82 82 (:REWRITE THE-FLOOR-ABOVE))
 (82 82
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (82 82
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (82 82
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (68 19 (:REWRITE DEFAULT-LOGIOR-1))
 (64 28 (:REWRITE DEFAULT-LOGAND-2))
 (60 60
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (60 60 (:REWRITE INTEGERP-<-CONSTANT))
 (60 60 (:REWRITE CONSTANT-<-INTEGERP))
 (60 60
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (60 60
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (60 60
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (60 60
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< c (- x))|))
 (60 60
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< (/ x) (/ y))|))
 (60 60 (:REWRITE |(< (- x) c)|))
 (60 60 (:REWRITE |(< (- x) (- y))|))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (56 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 8 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (36 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 3 (:REWRITE DEFAULT-MOD-RATIO))
 (32 32 (:REWRITE |(< x (+ c/d y))|))
 (31 31 (:REWRITE FOLD-CONSTS-IN-+))
 (28 28 (:REWRITE DEFAULT-LOGAND-1))
 (28 11 (:REWRITE DEFAULT-TIMES-1))
 (25 25 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (24 24 (:REWRITE RTL::BITS-NEG-INDICES))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:META META-INTEGERP-CORRECT))
 (20 6 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (13 13 (:REWRITE DEFAULT-MINUS))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 3 (:REWRITE |(* y x)|))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11 (:REWRITE DEFAULT-TIMES-2))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 4 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (8 4 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE DEFAULT-MOD-2))
 (3 3 (:REWRITE DEFAULT-MOD-1))
 (3 3 (:REWRITE |(mod x 2)| . 2))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE DEFAULT-DIVIDE))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(RTL::GEN-EXTEND-COR (96 5 (:DEFINITION EXPT))
                     (89 1 (:DEFINITION RTL::PROP))
                     (68 59 (:REWRITE DEFAULT-+-2))
                     (65 59 (:REWRITE DEFAULT-+-1))
                     (56 2 (:REWRITE RTL::NEG-BITN-0))
                     (38 29 (:REWRITE DEFAULT-<-1))
                     (37 29 (:REWRITE DEFAULT-<-2))
                     (32 16 (:REWRITE DEFAULT-*-2))
                     (30 8 (:REWRITE COMMUTATIVITY-OF-+))
                     (16 16 (:REWRITE DEFAULT-*-1))
                     (12 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
                     (9 5 (:REWRITE DEFAULT-UNARY-MINUS))
                     (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
                     (6 2 (:REWRITE RTL::NEG-BITN-1))
                     (6 2 (:REWRITE RTL::BVECP-BITN-0))
                     (3 3 (:REWRITE ZIP-OPEN))
                     (2 2 (:REWRITE RTL::BITN-NEG)))
(RTL::PROP-EXTEND (144 48 (:REWRITE RTL::BVECP-BITN-0))
                  (76 76 (:REWRITE DEFAULT-<-2))
                  (76 76 (:REWRITE DEFAULT-<-1))
                  (48 48 (:REWRITE RTL::NEG-BITN-1))
                  (48 48 (:REWRITE RTL::NEG-BITN-0))
                  (48 48 (:REWRITE RTL::BITN-NEG))
                  (42 42 (:REWRITE DEFAULT-+-2))
                  (42 42 (:REWRITE DEFAULT-+-1)))
(RTL::BITS-SUM
 (40879 58 (:LINEAR MOD-BOUNDS-1))
 (23541 106 (:REWRITE MOD-ZERO . 4))
 (21845 105 (:REWRITE MOD-X-Y-=-X . 3))
 (20788 106 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (19604 29 (:LINEAR RTL::MOD-BND-1))
 (16067 105 (:REWRITE MOD-X-Y-=-X . 4))
 (15172 101 (:REWRITE CANCEL-MOD-+))
 (13072 321
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (11940 106 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (9383 101 (:REWRITE RTL::MOD-DOES-NOTHING))
 (8250 110 (:REWRITE DEFAULT-MOD-RATIO))
 (7150 88 (:LINEAR RTL::FL-DEF))
 (6734
  6734
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6734
      6734
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6734
     6734
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6734 6734
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6734 6734
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5740 820 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (5740 820 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (5356 820
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5356 820
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (5330 460 (:REWRITE DEFAULT-TIMES-2))
 (5127 20
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4977 4977
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4977 4977
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4977 4977
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4250 105
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (4075 239
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3488 101 (:REWRITE |(integerp (- x))|))
 (3305 105 (:REWRITE MOD-X-Y-=-X . 2))
 (2964 106 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2964 106 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2690 101 (:REWRITE |(* (- x) y)|))
 (2360 236 (:REWRITE DEFAULT-DIVIDE))
 (2128 460 (:REWRITE DEFAULT-TIMES-1))
 (1781 334 (:REWRITE DEFAULT-LESS-THAN-1))
 (1679 101 (:REWRITE MOD-CANCEL-*-CONST))
 (1508 58 (:LINEAR MOD-BOUNDS-2))
 (1493 101
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1493 101
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1493 101
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1407 239
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1311 337 (:REWRITE DEFAULT-LESS-THAN-2))
 (1161 197 (:REWRITE SIMPLIFY-SUMS-<))
 (1084 51 (:LINEAR EXPT-<=-1-TWO))
 (1082 110 (:REWRITE DEFAULT-MOD-2))
 (1041 51 (:LINEAR EXPT->-1-ONE))
 (978 51 (:LINEAR EXPT->=-1-ONE))
 (924 51 (:LINEAR EXPT-X->=-X))
 (924 51 (:LINEAR EXPT-X->-X))
 (921 51 (:LINEAR EXPT-<-1-TWO))
 (909 3 (:REWRITE RTL::NEG-BITN-0))
 (822 210 (:META META-INTEGERP-CORRECT))
 (820 820 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (820 820
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (820 820
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (820 820
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (754 29 (:LINEAR MOD-BOUNDS-3))
 (666 666
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (557 13 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (498 56 (:REWRITE |(< (+ (- c) x) y)|))
 (482 110 (:REWRITE DEFAULT-MOD-1))
 (437 59 (:REWRITE |(< y (+ (- c) x))|))
 (437 35 (:REWRITE ODD-EXPT-THM))
 (337 337 (:REWRITE THE-FLOOR-BELOW))
 (337 337 (:REWRITE THE-FLOOR-ABOVE))
 (322 70 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (321 321
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (321 321
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (319 101
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (319 101
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (319 101
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (279 279 (:REWRITE FOLD-CONSTS-IN-+))
 (270 270 (:REWRITE DEFAULT-EXPT-1))
 (269 269 (:REWRITE |(expt 1/c n)|))
 (269 269 (:REWRITE |(expt (- x) n)|))
 (266 48 (:REWRITE ACL2-NUMBERP-X))
 (262 13 (:REWRITE RTL::BITS-NEG-INDICES))
 (242 2 (:REWRITE |(integerp (expt x n))|))
 (240 240
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (240 240 (:REWRITE INTEGERP-<-CONSTANT))
 (240 240 (:REWRITE CONSTANT-<-INTEGERP))
 (240 240
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (240 240
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (240 240
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (240 240
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (240 240 (:REWRITE |(< c (- x))|))
 (240 240
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (240 240
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (240 240
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (240 240
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (240 240 (:REWRITE |(< (/ x) (/ y))|))
 (240 240 (:REWRITE |(< (- x) c)|))
 (240 240 (:REWRITE |(< (- x) (- y))|))
 (216 19
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (216 19
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (210 210 (:REWRITE REDUCE-INTEGERP-+))
 (210 210 (:REWRITE INTEGERP-MINUS-X))
 (176 88 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (158 2 (:REWRITE |(< (if a b c) x)|))
 (106 106 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (102 102
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (102 102
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (102 102
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (102 102
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (101 101 (:REWRITE |(mod x (- y))| . 3))
 (101 101 (:REWRITE |(mod x (- y))| . 2))
 (101 101 (:REWRITE |(mod x (- y))| . 1))
 (101 101 (:REWRITE |(mod (- x) y)| . 3))
 (101 101 (:REWRITE |(mod (- x) y)| . 2))
 (101 101 (:REWRITE |(mod (- x) y)| . 1))
 (101 101 (:REWRITE |(- (* c x))|))
 (98 98 (:REWRITE |(< x (+ c/d y))|))
 (94 3 (:REWRITE |(* x (if a b c))|))
 (90 3 (:REWRITE RTL::NEG-BITN-1))
 (88 88 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (88 88 (:TYPE-PRESCRIPTION NATP))
 (88 88 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (88 88 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (88 88
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (88 88 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (82 34 (:REWRITE RATIONALP-X))
 (72 72 (:REWRITE |(< (+ c/d x) y)|))
 (70 70 (:REWRITE |(< 0 (* x y))|))
 (67 67 (:REWRITE |(< (* x y) 0)|))
 (64 64
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (64 64 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (59 3 (:REWRITE |(/ (if a b c))|))
 (58 29 (:LINEAR RTL::MOD-BND-2))
 (51 51 (:REWRITE |(< (/ x) 0)|))
 (51 51 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (51 51 (:LINEAR EXPT-LINEAR-UPPER-<))
 (51 51 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (51 51 (:LINEAR EXPT-LINEAR-LOWER-<))
 (51 51 (:LINEAR EXPT->=-1-TWO))
 (51 51 (:LINEAR EXPT->-1-TWO))
 (51 51 (:LINEAR EXPT-<=-1-ONE))
 (51 51 (:LINEAR EXPT-<-1-ONE))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (49 49 (:REWRITE |(< 0 (/ x))|))
 (44 44 (:LINEAR RTL::N<=FL-LINEAR))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (34 34 (:REWRITE REDUCE-RATIONALP-+))
 (34 34 (:REWRITE REDUCE-RATIONALP-*))
 (34 34 (:REWRITE RATIONALP-MINUS-X))
 (34 34 (:META META-RATIONALP-CORRECT))
 (29 29 (:LINEAR RTL::MOD-BND-3))
 (27 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (19 19 (:REWRITE |(equal c (/ x))|))
 (19 19 (:REWRITE |(equal c (- x))|))
 (19 19 (:REWRITE |(equal (/ x) c)|))
 (19 19 (:REWRITE |(equal (/ x) (/ y))|))
 (19 19 (:REWRITE |(equal (- x) c)|))
 (19 19 (:REWRITE |(equal (- x) (- y))|))
 (16 1 (:REWRITE RTL::BITS-TAIL))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (10 10
     (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
 (9 3 (:REWRITE RTL::BVECP-BITN-0))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE RTL::BITN-NEG))
 (2 1 (:REWRITE RTL::BITS-TAIL-GEN)))
(RTL::LEMMA
     (1485 93 (:REWRITE DEFAULT-PLUS-2))
     (975 207 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (907 207
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (907 207
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (831 831
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (831 831
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (831 831
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (408 204 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (225 33 (:REWRITE DEFAULT-LESS-THAN-1))
     (224 32 (:REWRITE SIMPLIFY-SUMS-<))
     (224 32
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (210 5 (:REWRITE CANCEL-MOD-+))
     (207 207 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (207 207 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (207 207
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (207 207
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (204 204
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (204 204 (:TYPE-PRESCRIPTION NATP))
     (204 204
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (204 204 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (204 204 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (204 204
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (192 32 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (175 5 (:REWRITE MOD-X-Y-=-X . 4))
     (175 5 (:REWRITE MOD-X-Y-=-X . 3))
     (170 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (155 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (130 5 (:REWRITE RTL::MOD-DOES-NOTHING))
     (127 93 (:REWRITE DEFAULT-PLUS-1))
     (120 5 (:REWRITE MOD-ZERO . 3))
     (96 88 (:REWRITE DEFAULT-TIMES-2))
     (90 5 (:REWRITE MOD-ZERO . 4))
     (88 88 (:REWRITE DEFAULT-TIMES-1))
     (80 5 (:REWRITE |(integerp (- x))|))
     (72 6 (:REWRITE DEFAULT-MOD-RATIO))
     (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (65 5 (:REWRITE |(* (- x) y)|))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (33 33 (:REWRITE THE-FLOOR-BELOW))
     (33 33 (:REWRITE THE-FLOOR-ABOVE))
     (33 33
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (33 33
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (33 33
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (33 33 (:REWRITE INTEGERP-<-CONSTANT))
     (33 33 (:REWRITE DEFAULT-LESS-THAN-2))
     (33 33 (:REWRITE CONSTANT-<-INTEGERP))
     (33 33
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (33 33
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (33 33 (:REWRITE |(< c (- x))|))
     (33 33
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (33 33
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (33 33 (:REWRITE |(< (/ x) (/ y))|))
     (33 33 (:REWRITE |(< (- x) c)|))
     (33 33 (:REWRITE |(< (- x) (- y))|))
     (30 30
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (28 28
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (28 28 (:REWRITE DEFAULT-DIVIDE))
     (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (25 5 (:REWRITE MOD-X-Y-=-X . 2))
     (25 5
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (25 5 (:REWRITE MOD-CANCEL-*-CONST))
     (25 5 (:REWRITE DEFAULT-MINUS))
     (25 5
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (25 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (25 5
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (25 5
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (19 19 (:REWRITE REDUCE-INTEGERP-+))
     (19 19 (:REWRITE INTEGERP-MINUS-X))
     (19 19 (:META META-INTEGERP-CORRECT))
     (11 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:REWRITE FOLD-CONSTS-IN-+))
     (8 2 (:REWRITE RATIONALP-X))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (7 7 (:REWRITE |(< 0 (/ x))|))
     (7 7 (:REWRITE |(< 0 (* x y))|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE DEFAULT-MOD-1))
     (6 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR)))
(RTL::BITS-SUM-SHIFT
 (19454 28 (:LINEAR MOD-BOUNDS-1))
 (12029 60 (:REWRITE MOD-ZERO . 4))
 (10533 60 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (9729 60 (:REWRITE MOD-X-Y-=-X . 3))
 (9501 60 (:REWRITE MOD-X-Y-=-X . 4))
 (9304 14 (:LINEAR RTL::MOD-BND-1))
 (8743 58 (:REWRITE CANCEL-MOD-+))
 (7511 56 (:REWRITE RTL::MOD-DOES-NOTHING))
 (5100 60 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4328 60 (:REWRITE DEFAULT-MOD-RATIO))
 (4238 212
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3930 70 (:LINEAR RTL::FL-DEF))
 (3667
  3667
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3667
      3667
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3667
     3667
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3667 3667
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3464 60 (:REWRITE MOD-ZERO . 3))
 (3251 150
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2991 281 (:REWRITE DEFAULT-TIMES-2))
 (2753 904 (:REWRITE DEFAULT-PLUS-2))
 (2387 341 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2387 341 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2387 341
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2387 341
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2359 60
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2347 2347
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2347 2347
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2347 2347
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2347 2347
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (2167 904 (:REWRITE DEFAULT-PLUS-1))
 (1977 60 (:REWRITE |(integerp (- x))|))
 (1819 60 (:REWRITE MOD-X-Y-=-X . 2))
 (1646 60 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1646 60 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1518 60 (:REWRITE |(* (- x) y)|))
 (1370 137 (:REWRITE DEFAULT-DIVIDE))
 (1219 622 (:REWRITE DEFAULT-MINUS))
 (1211 31 (:LINEAR EXPT-<=-1-TWO))
 (1203 281 (:REWRITE DEFAULT-TIMES-1))
 (1191 31 (:LINEAR EXPT-<-1-TWO))
 (1047 150
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1041 31 (:LINEAR EXPT-X->=-X))
 (1041 31 (:LINEAR EXPT-X->-X))
 (765 58 (:REWRITE MOD-CANCEL-*-CONST))
 (755 109 (:REWRITE SIMPLIFY-SUMS-<))
 (726 212 (:REWRITE DEFAULT-LESS-THAN-1))
 (720 28 (:LINEAR MOD-BOUNDS-2))
 (718 58
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (718 58
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (718 58
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (600 60 (:REWRITE DEFAULT-MOD-2))
 (595 212 (:REWRITE DEFAULT-LESS-THAN-2))
 (437 437
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (393 41 (:REWRITE |(< (+ (- c) x) y)|))
 (365 55 (:REWRITE |(< y (+ (- c) x))|))
 (360 14 (:LINEAR MOD-BOUNDS-3))
 (351 228 (:REWRITE |(+ c (+ d x))|))
 (341 341 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (341 341
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (341 341
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (341 341
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (321 31 (:LINEAR EXPT->=-1-ONE))
 (321 31 (:LINEAR EXPT->-1-ONE))
 (307 58
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (307 58
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (307 58
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (287 287
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (287 287
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (287 287
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (287 287
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (233 60 (:REWRITE DEFAULT-MOD-1))
 (213 61 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (212 212 (:REWRITE THE-FLOOR-BELOW))
 (212 212 (:REWRITE THE-FLOOR-ABOVE))
 (212 212
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (212 212
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (186 186 (:REWRITE FOLD-CONSTS-IN-+))
 (171 171 (:REWRITE DEFAULT-EXPT-2))
 (171 171 (:REWRITE DEFAULT-EXPT-1))
 (171 171 (:REWRITE |(expt 1/c n)|))
 (171 171 (:REWRITE |(expt (- x) n)|))
 (153 13
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (153 13
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (150 150
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (150 150 (:REWRITE INTEGERP-<-CONSTANT))
 (150 150 (:REWRITE CONSTANT-<-INTEGERP))
 (150 150
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (150 150
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (150 150
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (150 150
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (150 150 (:REWRITE |(< c (- x))|))
 (150 150
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (150 150
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (150 150
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (150 150
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (150 150 (:REWRITE |(< (/ x) (/ y))|))
 (150 150 (:REWRITE |(< (- x) c)|))
 (150 150 (:REWRITE |(< (- x) (- y))|))
 (146 27 (:REWRITE ODD-EXPT-THM))
 (89 89 (:REWRITE REDUCE-INTEGERP-+))
 (89 89 (:REWRITE INTEGERP-MINUS-X))
 (89 89 (:META META-INTEGERP-CORRECT))
 (86 86 (:REWRITE |(< x (+ c/d y))|))
 (70 70 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (67 67 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (62 62
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (62 62
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (62 62
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (62 62
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (60 60 (:REWRITE |(- (* c x))|))
 (58 58 (:REWRITE |(mod x (- y))| . 3))
 (58 58 (:REWRITE |(mod x (- y))| . 2))
 (58 58 (:REWRITE |(mod x (- y))| . 1))
 (58 58 (:REWRITE |(mod (- x) y)| . 3))
 (58 58 (:REWRITE |(mod (- x) y)| . 2))
 (58 58 (:REWRITE |(mod (- x) y)| . 1))
 (51 51 (:REWRITE |(< (+ c/d x) y)|))
 (46 46 (:REWRITE |(< 0 (* x y))|))
 (36 36 (:REWRITE |(< (* x y) 0)|))
 (35 35 (:REWRITE |(< 0 (/ x))|))
 (35 35 (:LINEAR RTL::N<=FL-LINEAR))
 (31 31 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (31 31 (:LINEAR EXPT-LINEAR-UPPER-<))
 (31 31 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (31 31 (:LINEAR EXPT-LINEAR-LOWER-<))
 (31 31 (:LINEAR EXPT->=-1-TWO))
 (31 31 (:LINEAR EXPT->-1-TWO))
 (31 31 (:LINEAR EXPT-<=-1-ONE))
 (31 31 (:LINEAR EXPT-<-1-ONE))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26 (:REWRITE |(< (/ x) 0)|))
 (24 14 (:LINEAR RTL::MOD-BND-2))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:LINEAR RTL::MOD-BND-3))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2)))
(RTL::LEMMA
 (20
   20
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (20
  20
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::LEMMA1
 (2720 189
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1531
  1531
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1531
      1531
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1531
     1531
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1531 1531
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1531 1531
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (626 417 (:REWRITE DEFAULT-PLUS-2))
 (587 417 (:REWRITE DEFAULT-PLUS-1))
 (544 15 (:LINEAR EXPT-X->=-X))
 (544 15 (:LINEAR EXPT-X->-X))
 (517 37 (:REWRITE RTL::BITS-NEG-INDICES))
 (401 15 (:LINEAR EXPT-<-1-TWO))
 (344 130
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (307 189 (:REWRITE DEFAULT-LESS-THAN-1))
 (305 189 (:REWRITE DEFAULT-LESS-THAN-2))
 (304 8 (:REWRITE ODD-EXPT-THM))
 (287 111 (:REWRITE SIMPLIFY-SUMS-<))
 (258 136 (:REWRITE |(< (- x) c)|))
 (220 26 (:REWRITE RTL::BITS-TAIL))
 (189 189 (:REWRITE THE-FLOOR-BELOW))
 (189 189 (:REWRITE THE-FLOOR-ABOVE))
 (189 189
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (189 189
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (136 136
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (136 136
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (136 136
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (136 136
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (136 136 (:REWRITE |(< c (- x))|))
 (136 136
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (136 136
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (136 136
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (136 136
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (136 136 (:REWRITE |(< (/ x) (/ y))|))
 (136 136 (:REWRITE |(< (- x) (- y))|))
 (132 132
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (132 132 (:REWRITE INTEGERP-<-CONSTANT))
 (132 132 (:REWRITE CONSTANT-<-INTEGERP))
 (128 128
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (80 8
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (80 8
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (77 26 (:REWRITE RTL::BITS-TAIL-GEN))
 (69 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (69 11
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (65 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (63 9 (:REWRITE DEFAULT-TIMES-1))
 (62 62 (:REWRITE |(< (+ c/d x) y)|))
 (61 61 (:REWRITE DEFAULT-EXPT-2))
 (61 61 (:REWRITE DEFAULT-EXPT-1))
 (61 61 (:REWRITE |(expt 1/c n)|))
 (61 61 (:REWRITE |(expt (- x) n)|))
 (60 60 (:REWRITE |(< x (+ c/d y))|))
 (59 59 (:REWRITE |arith (expt x c)|))
 (55 55 (:REWRITE |arith (expt 1/c n)|))
 (41 9 (:REWRITE DEFAULT-TIMES-2))
 (38 38 (:REWRITE |(< (* x y) 0)|))
 (37 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 36 (:REWRITE |(< y (+ (- c) x))|))
 (33 33 (:REWRITE REDUCE-INTEGERP-+))
 (33 33 (:REWRITE INTEGERP-MINUS-X))
 (33 33 (:META META-INTEGERP-CORRECT))
 (30 30
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (30 30
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (29 11 (:REWRITE DEFAULT-MINUS))
 (24 24 (:REWRITE |(< 0 (* x y))|))
 (20 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (20 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (18 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (18 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (18 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (18 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (16 4 (:REWRITE RTL::NEG-BITN-1))
 (16 4 (:REWRITE RTL::NEG-BITN-0))
 (15 15 (:LINEAR EXPT-LINEAR-UPPER-<))
 (15 15 (:LINEAR EXPT-LINEAR-LOWER-<))
 (15 15 (:LINEAR EXPT->=-1-TWO))
 (15 15 (:LINEAR EXPT->-1-TWO))
 (15 15 (:LINEAR EXPT-<=-1-ONE))
 (15 15 (:LINEAR EXPT-<-1-ONE))
 (14 14 (:REWRITE |arith (* c (* d x))|))
 (12 4 (:REWRITE RTL::BVECP-BITN-0))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11 11 (:REWRITE |(equal c (/ x))|))
 (11 11 (:REWRITE |(equal c (- x))|))
 (11 11 (:REWRITE |(equal (/ x) c)|))
 (11 11 (:REWRITE |(equal (/ x) (/ y))|))
 (11 11 (:REWRITE |(equal (- x) c)|))
 (11 11 (:REWRITE |(equal (- x) (- y))|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (10 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3G-EXPT-B))
 (10 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3F-EXPT-B))
 (10 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1G-EXPT-B))
 (10 1
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1F-EXPT-B))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |arith (* (- x) y)|))
 (5 5 (:REWRITE |arith (- (* c x))|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (5 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (5 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (5 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE RTL::BITN-NEG))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(- (- x))|))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2G-EXPT-B))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2F-EXPT-B))
 (1 1 (:REWRITE |arith (+ c (+ d x))|)))
(RTL::LEMMA2
     (35852 8 (:REWRITE FLOOR-=-X/Y . 4))
     (10529 10529
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (10529 10529
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (10529 10529
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5491 149 (:REWRITE DEFAULT-PLUS-2))
     (5091 67 (:REWRITE FLOOR-ZERO . 3))
     (4249 149 (:REWRITE DEFAULT-PLUS-1))
     (3729 67 (:REWRITE CANCEL-FLOOR-+))
     (3544 436 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3156 436
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3156 436
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3156 436
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3126 3126
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3126 3126
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3126 3126
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2949 70 (:REWRITE FLOOR-ZERO . 5))
     (2592 70 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (2415 483 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2282 338
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (2120 70 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (2094 1474 (:REWRITE DEFAULT-TIMES-1))
     (2058 30
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2058 30
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2007 483 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1904 70 (:REWRITE FLOOR-=-X/Y . 2))
     (1888 70 (:REWRITE FLOOR-=-X/Y . 3))
     (1859 483
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1859 483
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1796 436 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (1796 436 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (1796 436
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1758 1474 (:REWRITE DEFAULT-TIMES-2))
     (1600 87 (:REWRITE |(* (- x) y)|))
     (1328 83 (:REWRITE |(integerp (- x))|))
     (1307 399
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1254 402 (:REWRITE DEFAULT-LESS-THAN-1))
     (1227 399
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1219 70 (:REWRITE DEFAULT-FLOOR-RATIO))
     (966 483 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (870 402
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (820 18 (:REWRITE CANCEL-MOD-+))
     (816 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (799 21 (:REWRITE MOD-X-Y-=-X . 4))
     (772 24 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (722 334 (:REWRITE INTEGERP-MINUS-X))
     (719 21 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (676 24 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (642 330 (:REWRITE REDUCE-INTEGERP-+))
     (573 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (567 107 (:REWRITE DEFAULT-MINUS))
     (559 559
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (527 399 (:REWRITE SIMPLIFY-SUMS-<))
     (498 402 (:REWRITE DEFAULT-LESS-THAN-2))
     (490 21 (:REWRITE MOD-ZERO . 3))
     (483 483
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (483 483 (:TYPE-PRESCRIPTION NATP))
     (483 483 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (483 483 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (483 483
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (483 483
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (483 483
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (483 483 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (483 483 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (483 483
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (468 21 (:REWRITE MOD-ZERO . 4))
     (402 402 (:REWRITE THE-FLOOR-BELOW))
     (402 402 (:REWRITE THE-FLOOR-ABOVE))
     (402 402
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (402 402
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (402 402
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (402 402 (:REWRITE INTEGERP-<-CONSTANT))
     (402 402 (:REWRITE CONSTANT-<-INTEGERP))
     (402 402
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (402 402
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (402 402
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (402 402
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (402 402 (:REWRITE |(< c (- x))|))
     (402 402
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (402 402
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (402 402
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (402 402 (:REWRITE |(< (/ x) (/ y))|))
     (402 402 (:REWRITE |(< (- x) c)|))
     (402 402 (:REWRITE |(< (- x) (- y))|))
     (386 386
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (386 386 (:REWRITE DEFAULT-DIVIDE))
     (358 70 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (358 70 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (343 67 (:REWRITE FLOOR-ZERO . 2))
     (339 14 (:REWRITE RTL::MOD-DOES-NOTHING))
     (330 330 (:META META-INTEGERP-CORRECT))
     (323 67 (:REWRITE FLOOR-CANCEL-*-CONST))
     (305 21 (:REWRITE DEFAULT-MOD-RATIO))
     (301 20 (:REWRITE |(floor x 1)|))
     (284 164
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (284 164
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (232 8 (:REWRITE |(- (+ x y))|))
     (223 67
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (223 67
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (212 56
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (187 67
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (165 165 (:REWRITE |(< (/ x) 0)|))
     (165 165 (:REWRITE |(< (* x y) 0)|))
     (158 70 (:REWRITE DEFAULT-FLOOR-1))
     (123 123
          (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (112 88
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (112 88
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (106 18 (:REWRITE MOD-X-Y-=-X . 2))
     (106 18 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (106 18
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (105 21 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (105 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (99 67
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (91 91 (:REWRITE |(- (* c x))|))
     (90 18
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (89 89 (:REWRITE |(< 0 (/ x))|))
     (89 89 (:REWRITE |(< 0 (* x y))|))
     (86 18 (:REWRITE MOD-CANCEL-*-CONST))
     (81 81
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (74 18
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (70 70 (:REWRITE DEFAULT-FLOOR-2))
     (67 67 (:REWRITE |(floor x (- y))| . 2))
     (67 67 (:REWRITE |(floor x (- y))| . 1))
     (67 67 (:REWRITE |(floor (- x) y)| . 2))
     (67 67 (:REWRITE |(floor (- x) y)| . 1))
     (64 64
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (64 4 (:REWRITE |(mod x 1)|))
     (62 2 (:LINEAR RTL::MOD-BND-2))
     (48 2 (:LINEAR MOD-BOUNDS-3))
     (40 8 (:REWRITE |(- (- x))|))
     (38 38
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (38 38
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (37 21 (:REWRITE DEFAULT-MOD-1))
     (32 2 (:REWRITE |(floor (+ x r) i)|))
     (30 30
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (30 30
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (30 30
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (30 30 (:REWRITE |(equal c (/ x))|))
     (30 30 (:REWRITE |(equal c (- x))|))
     (30 30 (:REWRITE |(equal (/ x) c)|))
     (30 30 (:REWRITE |(equal (/ x) (/ y))|))
     (30 30 (:REWRITE |(equal (- x) c)|))
     (30 30 (:REWRITE |(equal (- x) (- y))|))
     (30 6
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (28 28
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (24 6 (:REWRITE RATIONALP-X))
     (21 21 (:REWRITE DEFAULT-MOD-2))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (20 20
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (20 20 (:REWRITE |(< (+ c/d x) y)|))
     (20 20 (:REWRITE |(< (+ (- c) x) y)|))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (18 18
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (18 18 (:REWRITE |(mod x (- y))| . 3))
     (18 18 (:REWRITE |(mod x (- y))| . 2))
     (18 18 (:REWRITE |(mod x (- y))| . 1))
     (18 18
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (18 18 (:REWRITE |(mod (- x) y)| . 3))
     (18 18 (:REWRITE |(mod (- x) y)| . 2))
     (18 18 (:REWRITE |(mod (- x) y)| . 1))
     (14 14
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (14 14
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (12 12
         (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (12 12
         (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
     (7 7
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (7 7
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (7 7
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (7 7
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (7 7
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (5 5 (:REWRITE |(equal (* x y) 0)|))
     (5 5 (:REWRITE |(+ c (+ d x))|))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (2 2
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::BITS-SUM-SWALLOW
 (30830 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (24976 12 (:LINEAR MOD-BOUNDS-1))
 (19937 290 (:LINEAR RTL::FL-DEF))
 (15707 30
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (15202 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (11842 24 (:REWRITE RTL::MOD-DOES-NOTHING))
 (11501 6 (:LINEAR RTL::MOD-BND-1))
 (7227 403
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5632 24 (:REWRITE MOD-ZERO . 4))
 (4010
  4010
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4010
      4010
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4010
     4010
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4010 4010
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4010 4010
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3990 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (3792 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (3642 24 (:REWRITE MOD-X-Y-=-X . 3))
 (3629 24 (:REWRITE MOD-X-Y-=-X . 4))
 (3603 24 (:REWRITE CANCEL-MOD-+))
 (2509 49 (:REWRITE ODD-EXPT-THM))
 (2152 24 (:REWRITE MOD-ZERO . 3))
 (2036 287 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2009 287 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1798 58 (:REWRITE RTL::FL+INT-REWRITE))
 (1555 1123 (:REWRITE DEFAULT-PLUS-2))
 (1527 21 (:LINEAR EXPT-<=-1-TWO))
 (1471 21 (:LINEAR EXPT-<-1-TWO))
 (1438 1438
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (1438 1438
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1438 1438
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1438 1438
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (1397 1123 (:REWRITE DEFAULT-PLUS-1))
 (1333 1333
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (1333 1333
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1331 1331
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1331 1331
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1331 1331
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1329 24 (:REWRITE DEFAULT-MOD-RATIO))
 (1316 287
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1316 287
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1308 21 (:LINEAR EXPT-X->=-X))
 (1308 21 (:LINEAR EXPT-X->-X))
 (1218 6 (:LINEAR RTL::MOD-BND-2))
 (1169 130 (:REWRITE DEFAULT-TIMES-2))
 (1168 146 (:REWRITE |(- (+ x y))|))
 (1082 58 (:REWRITE |(< (+ (- c) x) y)|))
 (1028 290
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (901 403 (:REWRITE DEFAULT-LESS-THAN-2))
 (860 24 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (860 24
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (834 24 (:REWRITE |(integerp (- x))|))
 (828 221 (:REWRITE SIMPLIFY-SUMS-<))
 (790 79 (:REWRITE DEFAULT-DIVIDE))
 (652 403 (:REWRITE DEFAULT-LESS-THAN-1))
 (644 24 (:REWRITE MOD-X-Y-=-X . 2))
 (641 24 (:REWRITE |(* (- x) y)|))
 (629 337 (:REWRITE DEFAULT-MINUS))
 (622 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (622 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (564 6 (:LINEAR MOD-BOUNDS-3))
 (473 101 (:REWRITE |(< y (+ (- c) x))|))
 (470 470
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (403 403 (:REWRITE THE-FLOOR-BELOW))
 (403 403 (:REWRITE THE-FLOOR-ABOVE))
 (403 403
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (403 403
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (390 24 (:REWRITE MOD-CANCEL-*-CONST))
 (342 130 (:REWRITE DEFAULT-TIMES-1))
 (312 24
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (312 24
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (312 24
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (312 12 (:LINEAR MOD-BOUNDS-2))
 (310 30
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (291 291
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (291 291 (:REWRITE INTEGERP-<-CONSTANT))
 (291 291 (:REWRITE CONSTANT-<-INTEGERP))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< c (- x))|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< (/ x) (/ y))|))
 (291 291 (:REWRITE |(< (- x) c)|))
 (291 291 (:REWRITE |(< (- x) (- y))|))
 (290 290 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (287 287 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (287 287
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (287 287
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (287 287
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (276 138 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (260 2 (:REWRITE RTL::NEG-BITN-0))
 (249 1
      (:REWRITE |(equal (mod a n) (mod b n))|))
 (240 24 (:REWRITE DEFAULT-MOD-2))
 (231 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (180 170 (:REWRITE INTEGERP-MINUS-X))
 (170 170 (:REWRITE REDUCE-INTEGERP-+))
 (170 170 (:META META-INTEGERP-CORRECT))
 (157 157 (:REWRITE |(< x (+ c/d y))|))
 (145 145 (:REWRITE FOLD-CONSTS-IN-+))
 (145 145 (:LINEAR RTL::N<=FL-LINEAR))
 (141 141 (:REWRITE DEFAULT-EXPT-2))
 (141 141 (:REWRITE DEFAULT-EXPT-1))
 (141 141 (:REWRITE |(expt 1/c n)|))
 (141 141 (:REWRITE |(expt (- x) n)|))
 (138 138
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (138 138 (:TYPE-PRESCRIPTION NATP))
 (138 138 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (138 138 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (138 138
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (120 120
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (120 120 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (118 24
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (118 24
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (118 24
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (91 91
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (88 70 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (86 86 (:REWRITE |(< 0 (* x y))|))
 (73 73 (:REWRITE |(< (* x y) 0)|))
 (73 73 (:REWRITE |(- (- x))|))
 (70 70 (:REWRITE |(< (+ c/d x) y)|))
 (61 61 (:REWRITE |(< (/ x) 0)|))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (60 2 (:REWRITE RTL::NEG-BITN-1))
 (54 54 (:REWRITE |(< 0 (/ x))|))
 (46 24 (:REWRITE DEFAULT-MOD-1))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (42 42
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (39 30 (:REWRITE |(equal (- x) (- y))|))
 (33 3
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (30 30
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (30 30
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (30 30 (:REWRITE |(equal c (/ x))|))
 (30 30 (:REWRITE |(equal c (- x))|))
 (30 30 (:REWRITE |(equal (/ x) c)|))
 (30 30 (:REWRITE |(equal (/ x) (/ y))|))
 (30 30 (:REWRITE |(equal (- x) c)|))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (25 25 (:REWRITE |(- (* c x))|))
 (24 24 (:REWRITE |(mod x (- y))| . 3))
 (24 24 (:REWRITE |(mod x (- y))| . 2))
 (24 24 (:REWRITE |(mod x (- y))| . 1))
 (24 24 (:REWRITE |(mod (- x) y)| . 3))
 (24 24 (:REWRITE |(mod (- x) y)| . 2))
 (24 24 (:REWRITE |(mod (- x) y)| . 1))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<))
 (21 21 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 21 (:LINEAR EXPT->=-1-TWO))
 (21 21 (:LINEAR EXPT->-1-TWO))
 (21 21 (:LINEAR EXPT-<=-1-ONE))
 (21 21 (:LINEAR EXPT-<-1-ONE))
 (18 18
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (6 6 (:LINEAR RTL::MOD-BND-3))
 (6 2 (:REWRITE RTL::BVECP-BITN-0))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE RTL::BITN-NEG)))
(RTL::LEMMA
 (3644 28 (:REWRITE RTL::BVECP-BITS-0))
 (694 14 (:REWRITE ODD-EXPT-THM))
 (545 123
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (538 28 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (502 148 (:REWRITE DEFAULT-LESS-THAN-2))
 (460 134
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (374 28 (:REWRITE RTL::BITS-NEG-INDICES))
 (310 10 (:LINEAR EXPT-<=-1-TWO))
 (300 10 (:LINEAR EXPT->-1-ONE))
 (265 123
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (260 10 (:LINEAR EXPT-X->=-X))
 (260 10 (:LINEAR EXPT-X->-X))
 (252 118 (:REWRITE SIMPLIFY-SUMS-<))
 (217 126 (:REWRITE |(< (- x) c)|))
 (182 128 (:REWRITE |(< c (- x))|))
 (167
  167
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (167 167
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (167
     167
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (167 167
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (167 167
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (167 167
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (163 26 (:REWRITE ACL2-NUMBERP-X))
 (150 20
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (148 148 (:REWRITE THE-FLOOR-BELOW))
 (148 148 (:REWRITE THE-FLOOR-ABOVE))
 (143 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (140 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (140 10 (:LINEAR EXPT->=-1-ONE))
 (134 134
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (134 134
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 128
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (128 128
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (128 128
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (128 128 (:REWRITE |(< (/ x) (/ y))|))
 (128 128 (:REWRITE |(< (- x) (- y))|))
 (123 123
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (123 123 (:REWRITE INTEGERP-<-CONSTANT))
 (123 123 (:REWRITE CONSTANT-<-INTEGERP))
 (102 93 (:REWRITE DEFAULT-PLUS-2))
 (77 13 (:REWRITE |(< (+ (- c) x) y)|))
 (61 19 (:REWRITE RATIONALP-X))
 (53 53 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (47 47 (:REWRITE INTEGERP-MINUS-X))
 (45 45 (:REWRITE DEFAULT-EXPT-1))
 (45 45 (:META META-INTEGERP-CORRECT))
 (44 44 (:REWRITE |(expt 1/c n)|))
 (44 44 (:REWRITE |(expt (- x) n)|))
 (40 40 (:REWRITE |(< 0 (* x y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (36 36 (:REWRITE |(< 0 (/ x))|))
 (34 34 (:REWRITE |(< (/ x) 0)|))
 (34 34 (:REWRITE |(< (* x y) 0)|))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (20 20
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (20 8 (:REWRITE |(+ c (+ d x))|))
 (19 19 (:REWRITE REDUCE-RATIONALP-+))
 (19 19 (:REWRITE REDUCE-RATIONALP-*))
 (19 19 (:REWRITE RATIONALP-MINUS-X))
 (19 19 (:META META-RATIONALP-CORRECT))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (10 10 (:LINEAR EXPT->=-1-TWO))
 (10 10 (:LINEAR EXPT->-1-TWO))
 (10 10 (:LINEAR EXPT-<=-1-ONE))
 (10 10 (:LINEAR EXPT-<-1-TWO))
 (10 10 (:LINEAR EXPT-<-1-ONE))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5 5 (:REWRITE |(- (- x))|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:TYPE-PRESCRIPTION NATP)))
(RTL::BITS-SUM-COR (10 6 (:REWRITE DEFAULT-+-1))
                   (9 6 (:REWRITE DEFAULT-+-2))
                   (8 5 (:REWRITE RTL::BITS-NEG-INDICES))
                   (5 5 (:REWRITE RTL::BITS-REVERSE-INDICES))
                   (3 3
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                   (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                   (2 1 (:REWRITE DEFAULT-<-1))
                   (1 1 (:REWRITE DEFAULT-<-2)))
(RTL::GEN-SUM-3
 (7663 1285 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (7663 1285 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (7423 1285
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (7423 1285
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6926 47 (:REWRITE CANCEL-MOD-+))
 (6339 50 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (6028 46 (:REWRITE RTL::MOD-DOES-NOTHING))
 (5341 5341
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5285 5285
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5285 5285
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5285 5285
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5071
  5071
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5071
      5071
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5071
     5071
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5071 5071
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3308 111 (:REWRITE DEFAULT-PLUS-2))
 (2528 111 (:REWRITE DEFAULT-PLUS-1))
 (2437 50 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2235 323
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2204 50 (:REWRITE DEFAULT-MOD-RATIO))
 (2084 322 (:REWRITE SIMPLIFY-SUMS-<))
 (2064 48 (:REWRITE |(integerp (- x))|))
 (2058 213 (:REWRITE DEFAULT-TIMES-2))
 (1939 47 (:REWRITE MOD-X-Y-=-X . 4))
 (1939 47 (:REWRITE MOD-X-Y-=-X . 3))
 (1922 337 (:REWRITE DEFAULT-LESS-THAN-1))
 (1598 47 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1598 47
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1490 149 (:REWRITE DEFAULT-DIVIDE))
 (1344 48 (:REWRITE |(* (- x) y)|))
 (1311 50 (:REWRITE MOD-ZERO . 4))
 (1291 337 (:REWRITE DEFAULT-LESS-THAN-2))
 (1285 1285 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1285 1285
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1285 1285
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1285 1285
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1250 50 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1250 50 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1175 47 (:REWRITE MOD-X-Y-=-X . 2))
 (894 149 (:REWRITE |(/ (expt x n))|))
 (831 198 (:REWRITE DEFAULT-MINUS))
 (752 47
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (752 47
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (752 47
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (738 9 (:LINEAR MOD-BOUNDS-3))
 (717 329
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (617 47 (:REWRITE MOD-CANCEL-*-CONST))
 (591 336
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (522 204 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (500 50 (:REWRITE DEFAULT-MOD-2))
 (450 18 (:LINEAR MOD-BOUNDS-2))
 (399 399
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (399 399
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (399 399
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (399 399
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (389 23 (:LINEAR EXPT-<=-1-TWO))
 (373 23 (:LINEAR EXPT-X->=-X))
 (373 23 (:LINEAR EXPT-X->-X))
 (338 329 (:REWRITE |(< (- x) (- y))|))
 (337 337 (:REWRITE THE-FLOOR-BELOW))
 (337 337 (:REWRITE THE-FLOOR-ABOVE))
 (336 336
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (336 336
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (329 329 (:REWRITE INTEGERP-<-CONSTANT))
 (329 329 (:REWRITE CONSTANT-<-INTEGERP))
 (329 329
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (329 329
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (329 329
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (329 329
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (329 329 (:REWRITE |(< c (- x))|))
 (329 329
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (329 329
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (329 329
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (329 329
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (329 329 (:REWRITE |(< (/ x) (/ y))|))
 (329 329 (:REWRITE |(< (- x) c)|))
 (302 262 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (269 213 (:REWRITE DEFAULT-TIMES-1))
 (262 262
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (262 262 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (248 8 (:LINEAR RTL::MOD-BND-2))
 (247 247 (:REWRITE DEFAULT-EXPT-2))
 (247 247 (:REWRITE DEFAULT-EXPT-1))
 (247 247 (:REWRITE |(expt 1/c n)|))
 (247 247 (:REWRITE |(expt (- x) n)|))
 (184 6 (:REWRITE |(* y x)|))
 (163 163
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (158 2 (:REWRITE |(* x (+ y z))|))
 (115 115 (:REWRITE REDUCE-INTEGERP-+))
 (115 115 (:REWRITE INTEGERP-MINUS-X))
 (115 115 (:META META-INTEGERP-CORRECT))
 (105 105 (:REWRITE |(< 0 (/ x))|))
 (105 105 (:REWRITE |(< 0 (* x y))|))
 (102 102
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (102 102
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (102 102 (:REWRITE |(< (* x y) 0)|))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (99 99 (:REWRITE |(< (/ x) 0)|))
 (89 23 (:LINEAR EXPT-<-1-TWO))
 (85 46
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (52 52
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (50 50 (:REWRITE DEFAULT-MOD-1))
 (48 48 (:REWRITE |(- (* c x))|))
 (47 47
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (47 47 (:REWRITE |(mod x (- y))| . 3))
 (47 47 (:REWRITE |(mod x (- y))| . 2))
 (47 47 (:REWRITE |(mod x (- y))| . 1))
 (47 47
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (47 47 (:REWRITE |(mod (- x) y)| . 3))
 (47 47 (:REWRITE |(mod (- x) y)| . 2))
 (47 47 (:REWRITE |(mod (- x) y)| . 1))
 (47 47
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (47 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (46 46
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (45 45
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (45 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (45 45
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (45 45
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (45 45
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (45 45
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (45 45
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (45 45 (:REWRITE |(equal c (/ x))|))
 (45 45 (:REWRITE |(equal c (- x))|))
 (45 45 (:REWRITE |(equal (/ x) c)|))
 (45 45 (:REWRITE |(equal (/ x) (/ y))|))
 (45 45 (:REWRITE |(equal (- x) c)|))
 (45 45 (:REWRITE |(equal (- x) (- y))|))
 (44 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (43 43
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 4 (:REWRITE RTL::BITS-TAIL))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<))
 (23 23 (:LINEAR EXPT-LINEAR-LOWER-<))
 (23 23 (:LINEAR EXPT->=-1-TWO))
 (23 23 (:LINEAR EXPT->-1-TWO))
 (23 23 (:LINEAR EXPT-<=-1-ONE))
 (23 23 (:LINEAR EXPT-<-1-ONE))
 (22 22 (:REWRITE |(< (+ c/d x) y)|))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (15 15 (:REWRITE |arith (expt x c)|))
 (14 14 (:REWRITE |arith (expt 1/c n)|))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:LINEAR RTL::MOD-BND-3))
 (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |arith (+ c (+ d x))|))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|)))
(RTL::BITS-SUM-3
 (152838 216 (:LINEAR MOD-BOUNDS-1))
 (90768 365 (:REWRITE MOD-ZERO . 4))
 (73042 363 (:REWRITE MOD-X-Y-=-X . 3))
 (73008 108 (:LINEAR RTL::MOD-BND-1))
 (62825 921
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (62666 365 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (55797 363 (:REWRITE MOD-X-Y-=-X . 4))
 (53103 354 (:REWRITE CANCEL-MOD-+))
 (50768 365 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (42321 374 (:REWRITE DEFAULT-MOD-RATIO))
 (30505 49
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (23359
  23359
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (23359
      23359
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (23359
     23359
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (23359 23359
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (23359 23359
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (21810 354 (:REWRITE RTL::MOD-DOES-NOTHING))
 (21196 3028 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (21196 3028 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (20170 3028
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (20170 3028
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (18842 1466 (:REWRITE DEFAULT-TIMES-2))
 (18145 18145
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18145 18145
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18145 18145
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (17859 210 (:LINEAR RTL::FL-DEF))
 (14496 363
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (12618 649
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12171 354 (:REWRITE |(integerp (- x))|))
 (11503 1466 (:REWRITE DEFAULT-TIMES-1))
 (11229 363 (:REWRITE MOD-X-Y-=-X . 2))
 (10581 24 (:REWRITE RTL::NEG-BITN-0))
 (10121 365 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (10121 365 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (9312 354 (:REWRITE |(* (- x) y)|))
 (7810 781 (:REWRITE DEFAULT-DIVIDE))
 (5955 354 (:REWRITE MOD-CANCEL-*-CONST))
 (5616 216 (:LINEAR MOD-BOUNDS-2))
 (5538 354
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5538 354
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (5538 354
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5365 3 (:REWRITE |(* x (if a b c))|))
 (4572 934 (:REWRITE DEFAULT-LESS-THAN-1))
 (4347 19 (:REWRITE |(* (if a b c) x)|))
 (4319 575 (:META META-INTEGERP-CORRECT))
 (4213 649
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4161 1205 (:REWRITE |(+ c (+ d x))|))
 (3863 374 (:REWRITE DEFAULT-MOD-1))
 (3704 374 (:REWRITE DEFAULT-MOD-2))
 (3268 154 (:LINEAR EXPT-<=-1-TWO))
 (3250 152 (:LINEAR EXPT->-1-ONE))
 (3088 937 (:REWRITE DEFAULT-LESS-THAN-2))
 (3028 3028 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3028 3028
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3028 3028
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3028 3028
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3021 558 (:REWRITE SIMPLIFY-SUMS-<))
 (2987 152 (:LINEAR EXPT-X->=-X))
 (2987 152 (:LINEAR EXPT-X->-X))
 (2808 108 (:LINEAR MOD-BOUNDS-3))
 (2422 152 (:LINEAR EXPT->=-1-ONE))
 (2040 2040
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1892 152 (:LINEAR EXPT-<-1-TWO))
 (1516 1516
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (1516 1516
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1516 1516
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1516 1516
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (1006 154 (:REWRITE |(< (+ (- c) x) y)|))
 (947 947 (:REWRITE FOLD-CONSTS-IN-+))
 (944 944 (:REWRITE DEFAULT-EXPT-1))
 (943 943 (:REWRITE |(expt 1/c n)|))
 (943 943 (:REWRITE |(expt (- x) n)|))
 (937 937 (:REWRITE THE-FLOOR-BELOW))
 (937 937 (:REWRITE THE-FLOOR-ABOVE))
 (921 921
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (921 921
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (871 115 (:REWRITE |(< y (+ (- c) x))|))
 (834 78 (:REWRITE ODD-EXPT-THM))
 (819 354
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (819 354
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (819 354
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (810 171 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (736 24 (:REWRITE RTL::NEG-BITN-1))
 (672 6 (:REWRITE |(integerp (expt x n))|))
 (649 649
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (649 649 (:REWRITE INTEGERP-<-CONSTANT))
 (649 649 (:REWRITE CONSTANT-<-INTEGERP))
 (649 649
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (649 649
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (649 649
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (649 649
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (649 649 (:REWRITE |(< c (- x))|))
 (649 649
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (649 649
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (649 649
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (649 649
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (649 649 (:REWRITE |(< (/ x) (/ y))|))
 (649 649 (:REWRITE |(< (- x) c)|))
 (649 649 (:REWRITE |(< (- x) (- y))|))
 (634 45
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (634 45
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (616 304
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (575 575 (:REWRITE REDUCE-INTEGERP-+))
 (575 575 (:REWRITE INTEGERP-MINUS-X))
 (561 17 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (451 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (382 304
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (366 183 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (354 354 (:REWRITE |(mod x (- y))| . 3))
 (354 354 (:REWRITE |(mod x (- y))| . 2))
 (354 354 (:REWRITE |(mod x (- y))| . 1))
 (354 354 (:REWRITE |(mod (- x) y)| . 3))
 (354 354 (:REWRITE |(mod (- x) y)| . 2))
 (354 354 (:REWRITE |(mod (- x) y)| . 1))
 (354 354 (:REWRITE |(- (* c x))|))
 (304 304
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (304 304
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (301 301 (:REWRITE |(< x (+ c/d y))|))
 (290 54 (:REWRITE ACL2-NUMBERP-X))
 (286 154 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (266 17 (:REWRITE RTL::BITS-NEG-INDICES))
 (264 264 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (216 108 (:LINEAR RTL::MOD-BND-2))
 (210 210 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (198 6 (:DEFINITION NATP))
 (189 189 (:REWRITE |(< (+ c/d x) y)|))
 (186 186 (:REWRITE |(< 0 (* x y))|))
 (183 183
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (183 183 (:TYPE-PRESCRIPTION NATP))
 (183 183 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (183 183 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (183 183
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (175 175 (:REWRITE |(< (* x y) 0)|))
 (171 171
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (171 171 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (158 2 (:REWRITE |(< (if a b c) x)|))
 (154 154 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (154 154 (:LINEAR EXPT-LINEAR-UPPER-<))
 (154 154 (:LINEAR EXPT-LINEAR-LOWER-<))
 (152 152 (:LINEAR EXPT->=-1-TWO))
 (152 152 (:LINEAR EXPT->-1-TWO))
 (152 152 (:LINEAR EXPT-<=-1-ONE))
 (152 152 (:LINEAR EXPT-<-1-ONE))
 (140 140 (:REWRITE |(< (/ x) 0)|))
 (135 135
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (135 135
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (108 108 (:LINEAR RTL::MOD-BND-3))
 (105 105 (:LINEAR RTL::N<=FL-LINEAR))
 (88 88 (:REWRITE |(< 0 (/ x))|))
 (88 37 (:REWRITE RATIONALP-X))
 (80 80
     (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
 (73 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (72 24 (:REWRITE RTL::BVECP-BITN-0))
 (64 64
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (64 64
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (59 3 (:REWRITE |(/ (if a b c))|))
 (49 49
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (45 45
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (45 45 (:REWRITE |(equal c (/ x))|))
 (45 45 (:REWRITE |(equal c (- x))|))
 (45 45 (:REWRITE |(equal (/ x) c)|))
 (45 45 (:REWRITE |(equal (/ x) (/ y))|))
 (45 45 (:REWRITE |(equal (- x) c)|))
 (45 45 (:REWRITE |(equal (- x) (- y))|))
 (44 2 (:REWRITE |(* x (expt x n))|))
 (37 37 (:REWRITE REDUCE-RATIONALP-+))
 (37 37 (:REWRITE REDUCE-RATIONALP-*))
 (37 37 (:REWRITE RATIONALP-MINUS-X))
 (37 37 (:META META-RATIONALP-CORRECT))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (29 29
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (24 24 (:REWRITE RTL::BITN-NEG))
 (16 1 (:REWRITE RTL::BITS-TAIL))
 (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(* 0 x)|))
 (1 1 (:REWRITE EXPT-X->-X)))
(RTL::LEMMA
 (4301 647 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (4229 647
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (4229 647
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2698 2698
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (2682 2682
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2682 2682
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2682 2682
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1740 12 (:REWRITE CANCEL-MOD-+))
 (1696
   1696
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1696
  1696
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1696
      1696
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1696
     1696
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1696 1696
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1696 1696
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1162 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1062 12 (:REWRITE RTL::MOD-DOES-NOTHING))
 (660 12 (:REWRITE MOD-ZERO . 3))
 (647 647 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (647 647
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (647 647
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (637 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (541 76
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (541 76 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (529 76 (:REWRITE SIMPLIFY-SUMS-<))
 (518 14 (:REWRITE DEFAULT-MOD-RATIO))
 (516 12 (:REWRITE |(integerp (- x))|))
 (500 10
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (500 10
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (489 489
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (468 12 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (464 50 (:REWRITE DEFAULT-TIMES-2))
 (462 38 (:REWRITE DEFAULT-LOGIOR-2))
 (462 38 (:REWRITE DEFAULT-LOGIOR-1))
 (436 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (408 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (408 12
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (372 12 (:REWRITE MOD-X-Y-=-X . 4))
 (372 12 (:REWRITE MOD-X-Y-=-X . 3))
 (369 52 (:REWRITE DEFAULT-PLUS-2))
 (358 85
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (349 85 (:REWRITE DEFAULT-LESS-THAN-1))
 (340 34 (:REWRITE DEFAULT-DIVIDE))
 (336 12 (:REWRITE |(* (- x) y)|))
 (326 21 (:REWRITE ODD-EXPT-THM))
 (300 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (300 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (300 12 (:REWRITE MOD-X-Y-=-X . 2))
 (286 85 (:REWRITE DEFAULT-LESS-THAN-2))
 (272 52 (:REWRITE DEFAULT-PLUS-1))
 (236 12 (:REWRITE MOD-ZERO . 4))
 (204 34 (:REWRITE |(/ (expt x n))|))
 (202 46 (:REWRITE DEFAULT-MINUS))
 (192 12
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (192 12
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (192 12
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (164 2 (:LINEAR MOD-BOUNDS-3))
 (160 7 (:LINEAR EXPT-X->=-X))
 (160 7 (:LINEAR EXPT-X->-X))
 (132 12 (:REWRITE MOD-CANCEL-*-CONST))
 (122 14 (:REWRITE DEFAULT-MOD-2))
 (121 121
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (121 121
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (121 121
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (107 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (100 4 (:LINEAR MOD-BOUNDS-2))
 (92 92
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (92 92
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (92 92
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (92 92
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (89 7 (:LINEAR EXPT-<=-1-TWO))
 (85 85 (:REWRITE THE-FLOOR-BELOW))
 (85 85 (:REWRITE THE-FLOOR-ABOVE))
 (85 85
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (85 85
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (76 76
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (76 76 (:REWRITE INTEGERP-<-CONSTANT))
 (76 76 (:REWRITE CONSTANT-<-INTEGERP))
 (76 76
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (76 76
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (76 76
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (76 76
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (76 76 (:REWRITE |(< c (- x))|))
 (76 76
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (76 76
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (76 76
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (76 76
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (76 76 (:REWRITE |(< (/ x) (/ y))|))
 (76 76 (:REWRITE |(< (- x) c)|))
 (76 76 (:REWRITE |(< (- x) (- y))|))
 (67 67 (:REWRITE DEFAULT-EXPT-2))
 (67 67 (:REWRITE DEFAULT-EXPT-1))
 (67 67 (:REWRITE |(expt 1/c n)|))
 (67 67 (:REWRITE |(expt (- x) n)|))
 (62 2 (:LINEAR RTL::MOD-BND-2))
 (50 50 (:REWRITE DEFAULT-TIMES-1))
 (48 24 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (48 12 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (34 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (34 34
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (27 27 (:REWRITE REDUCE-INTEGERP-+))
 (27 27 (:REWRITE INTEGERP-MINUS-X))
 (27 27 (:META META-INTEGERP-CORRECT))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (24 24
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (24 24 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (24 24 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (24 24 (:TYPE-PRESCRIPTION NATP))
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (24 24
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (21 21 (:REWRITE |(< 0 (/ x))|))
 (20 4 (:REWRITE RTL::BITS-TAIL))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (19 19 (:REWRITE |(< (/ x) 0)|))
 (19 19 (:REWRITE |(< (* x y) 0)|))
 (14 14 (:REWRITE DEFAULT-MOD-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE |(mod x (- y))| . 3))
 (12 12 (:REWRITE |(mod x (- y))| . 2))
 (12 12 (:REWRITE |(mod x (- y))| . 1))
 (12 12
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (12 12 (:REWRITE |(mod (- x) y)| . 3))
 (12 12 (:REWRITE |(mod (- x) y)| . 2))
 (12 12 (:REWRITE |(mod (- x) y)| . 1))
 (12 12
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (12 12 (:REWRITE |(- (* c x))|))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE NORMALIZE-ADDENDS))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 2 (:REWRITE |(* y x)|))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:LINEAR EXPT->=-1-TWO))
 (7 7 (:LINEAR EXPT->-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(* 1 x)|))
 (2 2 (:LINEAR RTL::MOD-BND-3))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::BITS-SUM-PLUS-1
 (40879 58 (:LINEAR MOD-BOUNDS-1))
 (39331 145 (:REWRITE RTL::MOD-DOES-NOTHING))
 (38472 700 (:LINEAR RTL::FL-DEF))
 (36141 159 (:REWRITE MOD-ZERO . 4))
 (29850 159 (:REWRITE MOD-X-Y-=-X . 3))
 (29655 1149
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (27525 159 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (24508 155 (:REWRITE CANCEL-MOD-+))
 (24016 159 (:REWRITE MOD-X-Y-=-X . 4))
 (20226 159 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (19604 29 (:LINEAR RTL::MOD-BND-1))
 (16028 3735 (:REWRITE DEFAULT-PLUS-2))
 (13169
  13169
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13169
      13169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13169
     13169
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13169 13169
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12122 159 (:REWRITE DEFAULT-MOD-RATIO))
 (11901 159 (:REWRITE MOD-ZERO . 3))
 (9914 3735 (:REWRITE DEFAULT-PLUS-1))
 (9072 1296 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (9072 1296 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (8544 1296
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (8544 1296
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (8152 769 (:REWRITE DEFAULT-TIMES-2))
 (7632 7632
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7624 7624
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7624 7624
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7624 7624
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6352 154 (:LINEAR EXPT-<=-1-TWO))
 (6214 159
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (5664 165 (:REWRITE |(integerp (- x))|))
 (5664 154 (:LINEAR EXPT-<-1-TWO))
 (5630 68
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5286 152 (:LINEAR EXPT-X->=-X))
 (5286 152 (:LINEAR EXPT-X->-X))
 (4783 159 (:REWRITE MOD-X-Y-=-X . 2))
 (4352 159 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (4352 159 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4304 167 (:REWRITE |(* (- x) y)|))
 (4027 817
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3987 1151 (:REWRITE DEFAULT-LESS-THAN-1))
 (3950 395 (:REWRITE DEFAULT-DIVIDE))
 (3622 1738 (:REWRITE DEFAULT-MINUS))
 (3503 631 (:REWRITE SIMPLIFY-SUMS-<))
 (3172 10 (:REWRITE RTL::NEG-BITN-0))
 (3158 769 (:REWRITE DEFAULT-TIMES-1))
 (2800 2800
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (2800 2800
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (2800 2800
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (2800 2800
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (2717 1151 (:REWRITE DEFAULT-LESS-THAN-2))
 (2290 2 (:DEFINITION RTL::GEN))
 (1798 198 (:REWRITE |(< (+ (- c) x) y)|))
 (1752 155 (:REWRITE MOD-CANCEL-*-CONST))
 (1675 1675
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1670 244 (:REWRITE |(< y (+ (- c) x))|))
 (1602 2 (:DEFINITION RTL::PROP))
 (1590 159 (:REWRITE DEFAULT-MOD-2))
 (1547 155
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1547 155
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1547 155
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1508 58 (:LINEAR MOD-BOUNDS-2))
 (1430 304
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (1296 1296 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1296 1296
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1296 1296
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1296 1296
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1247 155
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1247 155
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1247 155
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1219 346 (:META META-INTEGERP-CORRECT))
 (1151 1151 (:REWRITE THE-FLOOR-BELOW))
 (1151 1151 (:REWRITE THE-FLOOR-ABOVE))
 (1149 1149
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1149 1149
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1009 823 (:REWRITE |(< (- x) c)|))
 (841 823 (:REWRITE |(< (- x) (- y))|))
 (823 823
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (823 823
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (823 823
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (823 823
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (823 823 (:REWRITE |(< c (- x))|))
 (823 823
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (823 823
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (823 823
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (823 823
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (823 823 (:REWRITE |(< (/ x) (/ y))|))
 (817 817
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (817 817 (:REWRITE INTEGERP-<-CONSTANT))
 (817 817 (:REWRITE CONSTANT-<-INTEGERP))
 (754 29 (:LINEAR MOD-BOUNDS-3))
 (702 130 (:REWRITE ODD-EXPT-THM))
 (700 700 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (644 644 (:REWRITE DEFAULT-EXPT-2))
 (644 644 (:REWRITE DEFAULT-EXPT-1))
 (644 644 (:REWRITE |(expt 1/c n)|))
 (644 644 (:REWRITE |(expt (- x) n)|))
 (636 636 (:REWRITE FOLD-CONSTS-IN-+))
 (590 159 (:REWRITE DEFAULT-MOD-1))
 (528 222 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (510 6 (:REWRITE |(integerp (expt x n))|))
 (424 424 (:REWRITE |(< x (+ c/d y))|))
 (388 154 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (350 350 (:LINEAR RTL::N<=FL-LINEAR))
 (346 346 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (346 346 (:REWRITE REDUCE-INTEGERP-+))
 (346 346 (:REWRITE INTEGERP-MINUS-X))
 (320 66
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (320 66
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (304 304
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (304 304
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (304 304
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (300 10 (:REWRITE RTL::NEG-BITN-1))
 (257 257 (:REWRITE |(< 0 (* x y))|))
 (248 248 (:REWRITE |(< (+ c/d x) y)|))
 (196 196 (:REWRITE |(< (* x y) 0)|))
 (185 185 (:REWRITE |(< 0 (/ x))|))
 (176 88 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (165 165 (:REWRITE |(- (* c x))|))
 (155 155 (:REWRITE |(mod x (- y))| . 3))
 (155 155 (:REWRITE |(mod x (- y))| . 2))
 (155 155 (:REWRITE |(mod x (- y))| . 1))
 (155 155 (:REWRITE |(mod (- x) y)| . 3))
 (155 155 (:REWRITE |(mod (- x) y)| . 2))
 (155 155 (:REWRITE |(mod (- x) y)| . 1))
 (154 154 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (154 154 (:LINEAR EXPT-LINEAR-UPPER-<))
 (154 154 (:LINEAR EXPT-LINEAR-LOWER-<))
 (154 154 (:LINEAR EXPT->=-1-TWO))
 (154 154 (:LINEAR EXPT->-1-TWO))
 (154 154 (:LINEAR EXPT-<=-1-ONE))
 (154 154 (:LINEAR EXPT-<-1-ONE))
 (146 146 (:REWRITE |(< (/ x) 0)|))
 (140 140
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (140 140
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (132 4 (:DEFINITION NATP))
 (97 97
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (97 97
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (88 88
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (88 88 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (88 88 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (88 88 (:TYPE-PRESCRIPTION NATP))
 (88 88 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (88 88 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (88 88
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (80 66 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (68 68
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (66 66
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (66 66 (:REWRITE |(equal c (/ x))|))
 (66 66 (:REWRITE |(equal c (- x))|))
 (66 66 (:REWRITE |(equal (/ x) c)|))
 (66 66 (:REWRITE |(equal (/ x) (/ y))|))
 (66 66 (:REWRITE |(equal (- x) c)|))
 (66 66 (:REWRITE |(equal (- x) (- y))|))
 (58 58
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (58 29 (:LINEAR RTL::MOD-BND-2))
 (40 40
     (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
 (30 10 (:REWRITE RTL::BVECP-BITN-0))
 (29 29 (:LINEAR RTL::MOD-BND-3))
 (22 2 (:REWRITE |(* -1 x)|))
 (17 17
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:REWRITE RTL::BITN-NEG))
 (8 8
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (8 8
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2)))
(RTL::MY-INDUCT (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (30 6
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)))
(RTL::SUM-WHEN-LOGAND=0
 (7155
  7155
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7155
      7155
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7155
     7155
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7155 7155
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7155 7155
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3276 3276
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3276 3276
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3276 3276
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3276 3276
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2107 2107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2107 2107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2107 2107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1926 344
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1770 1234 (:REWRITE DEFAULT-TIMES-2))
 (1418 1418
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1394 178 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1343 254
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1256 1234 (:REWRITE DEFAULT-TIMES-1))
 (1235 254 (:REWRITE SIMPLIFY-SUMS-<))
 (1145 585 (:REWRITE DEFAULT-PLUS-2))
 (1108 280
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1087 360 (:REWRITE DEFAULT-LESS-THAN-2))
 (1020 132 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1008 360 (:REWRITE DEFAULT-LESS-THAN-1))
 (940 140
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (940 140
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (875 585 (:REWRITE DEFAULT-PLUS-1))
 (868 132
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (738 23 (:LINEAR EXPT-X->=-X))
 (738 23 (:LINEAR EXPT-X->-X))
 (700 140 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (700 140
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (700 140
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (700 140
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (700 140
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (660 132 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (660 132
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (660 132
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (660 132
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (601 73 (:REWRITE ODD-EXPT-THM))
 (526 94
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (433 23 (:LINEAR EXPT-<=-1-TWO))
 (360 360 (:REWRITE THE-FLOOR-BELOW))
 (360 360 (:REWRITE THE-FLOOR-ABOVE))
 (356 344
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (356 344
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (280 280 (:REWRITE INTEGERP-<-CONSTANT))
 (280 280 (:REWRITE CONSTANT-<-INTEGERP))
 (280 280
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (280 280
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (280 280
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (280 280
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (280 280 (:REWRITE |(< c (- x))|))
 (280 280
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (280 280
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (280 280
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (280 280
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (280 280 (:REWRITE |(< (/ x) (/ y))|))
 (280 280 (:REWRITE |(< (- x) c)|))
 (280 280 (:REWRITE |(< (- x) (- y))|))
 (257 257 (:REWRITE LOGAND-CONSTANT-MASK))
 (252 252
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (252 252 (:REWRITE NORMALIZE-ADDENDS))
 (238 238 (:REWRITE ZIP-OPEN))
 (190 178 (:REWRITE DEFAULT-FLOOR-1))
 (178 178 (:REWRITE DEFAULT-FLOOR-2))
 (178 178 (:REWRITE |(floor x 2)| . 2))
 (160 160 (:REWRITE DEFAULT-EXPT-2))
 (160 160 (:REWRITE DEFAULT-EXPT-1))
 (160 160 (:REWRITE |(expt 1/c n)|))
 (160 160 (:REWRITE |(expt (- x) n)|))
 (119 119 (:REWRITE REDUCE-INTEGERP-+))
 (119 119 (:REWRITE INTEGERP-MINUS-X))
 (119 119 (:META META-INTEGERP-CORRECT))
 (75 75 (:REWRITE |(< (/ x) 0)|))
 (75 75 (:REWRITE |(< (* x y) 0)|))
 (57 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (57 17
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (55 55
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (55 55
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (54 54 (:REWRITE |(< y (+ (- c) x))|))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (46 46
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (46 46
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (44 44 (:REWRITE |(< 0 (* x y))|))
 (40 40 (:REWRITE FOLD-CONSTS-IN-+))
 (24 24 (:LINEAR EXPT-LINEAR-LOWER-<))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<))
 (23 23 (:LINEAR EXPT->=-1-TWO))
 (23 23 (:LINEAR EXPT->-1-TWO))
 (23 23 (:LINEAR EXPT-<=-1-ONE))
 (23 23 (:LINEAR EXPT-<-1-TWO))
 (23 23 (:LINEAR EXPT-<-1-ONE))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17 (:REWRITE |(equal c (/ x))|))
 (17 17 (:REWRITE |(equal c (- x))|))
 (17 17 (:REWRITE |(equal (/ x) c)|))
 (17 17 (:REWRITE |(equal (/ x) (/ y))|))
 (17 17 (:REWRITE |(equal (- x) c)|))
 (17 17 (:REWRITE |(equal (- x) (- y))|))
 (16 16 (:REWRITE ZP-OPEN))
 (13 13 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (13 13 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (12 12 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10 (:REWRITE |arith (expt x c)|))
 (10 10 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (8 8 (:REWRITE |arith (expt 1/c n)|))
 (7 7 (:REWRITE |(equal x (if a b c))|))
 (7 7 (:REWRITE |(equal (if a b c) x)|))
 (6 6
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (6 6
    (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
 (6 6
    (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
 (6 6
    (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 4 (:REWRITE |arith (+ c (+ d x))|)))
(RTL::LOGAND-GEN-0 (70 3 (:DEFINITION EXPT))
                   (35 30 (:REWRITE DEFAULT-+-2))
                   (33 30 (:REWRITE DEFAULT-+-1))
                   (32 18 (:REWRITE FOLD-CONSTS-IN-+))
                   (29 5 (:REWRITE COMMUTATIVITY-OF-+))
                   (22 16 (:REWRITE DEFAULT-<-2))
                   (22 16 (:REWRITE DEFAULT-<-1))
                   (22 12 (:REWRITE RTL::BITS-NEG-INDICES))
                   (17 7 (:REWRITE DEFAULT-*-2))
                   (12 12 (:REWRITE RTL::BITS-REVERSE-INDICES))
                   (7 7 (:REWRITE DEFAULT-*-1))
                   (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                   (4 2 (:REWRITE UNICITY-OF-0))
                   (2 2 (:REWRITE ZIP-OPEN))
                   (2 2 (:DEFINITION FIX)))
(RTL::LOGAND-GEN-0-COR
     (177 6 (:REWRITE RTL::NEG-BITN-0))
     (81 6 (:DEFINITION EXPT))
     (51 39 (:REWRITE DEFAULT-<-2))
     (42 42
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (42 42
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (39 39 (:REWRITE DEFAULT-<-1))
     (34 30 (:REWRITE DEFAULT-+-2))
     (34 30 (:REWRITE DEFAULT-+-1))
     (28 16 (:REWRITE RTL::BITS-NEG-INDICES))
     (22 6 (:REWRITE FOLD-CONSTS-IN-+))
     (21 6 (:REWRITE COMMUTATIVITY-OF-+))
     (18 16 (:REWRITE RTL::BITS-REVERSE-INDICES))
     (18 6 (:REWRITE RTL::NEG-BITN-1))
     (18 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (18 6 (:REWRITE DEFAULT-*-2))
     (18 6 (:REWRITE RTL::BVECP-BITN-0))
     (16 2 (:REWRITE RTL::BITS-TAIL))
     (9 3 (:DEFINITION NATP))
     (8 8
        (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
     (6 6 (:REWRITE ZIP-OPEN))
     (6 6 (:REWRITE DEFAULT-*-1))
     (6 6 (:REWRITE RTL::BITN-NEG))
     (6 2 (:REWRITE RTL::BITS-TAIL-GEN))
     (6 2 (:LINEAR RTL::LOGAND-BND))
     (4 2 (:REWRITE UNICITY-OF-0))
     (2 2 (:DEFINITION FIX))
     (1 1 (:TYPE-PRESCRIPTION NATP)))
(RTL::GEN-PLUS
 (16818 42 (:REWRITE RTL::NEG-BITN-0))
 (13856 42 (:REWRITE RTL::BVECP-BITN-0))
 (13369 1929 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (10939 79 (:REWRITE RTL::MOD-DOES-NOTHING))
 (10817 79 (:REWRITE CANCEL-MOD-+))
 (10194 79 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (9837
  9837
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9837
      9837
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9837
     9837
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9837 9837
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9837 9837
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9558 1394
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7130 1930
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (7130 1930
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (7041 7041
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7041 7041
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7041 7041
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7017 7017
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6824 18 (:REWRITE RTL::BITS-TAIL))
 (6006 79 (:REWRITE MOD-ZERO . 3))
 (4742 18 (:REWRITE RTL::BITS-TAIL-GEN))
 (4639 1394
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4433 1481
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4425 1481 (:REWRITE DEFAULT-LESS-THAN-2))
 (4418 1380 (:REWRITE SIMPLIFY-SUMS-<))
 (4218 79 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (3692 79 (:REWRITE DEFAULT-MOD-RATIO))
 (3659 79 (:REWRITE MOD-X-Y-=-X . 3))
 (3554 79 (:REWRITE MOD-X-Y-=-X . 4))
 (3497 167 (:LINEAR EXPT-<=-1-TWO))
 (3393 354 (:REWRITE DEFAULT-TIMES-2))
 (2922 244 (:REWRITE |(/ (expt x n))|))
 (2758 79 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2758 79
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2705 754 (:REWRITE DEFAULT-PLUS-2))
 (2557 79 (:REWRITE |(integerp (- x))|))
 (2450 245 (:REWRITE DEFAULT-DIVIDE))
 (2363 79 (:REWRITE MOD-ZERO . 4))
 (2118 754 (:REWRITE DEFAULT-PLUS-1))
 (2112 79 (:REWRITE |(* (- x) y)|))
 (2100 1059 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (2047 79 (:REWRITE MOD-X-Y-=-X . 2))
 (2011 79 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2011 79 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1996 234 (:REWRITE ODD-EXPT-THM))
 (1962 1481 (:REWRITE DEFAULT-LESS-THAN-1))
 (1930 1930 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1930 1930
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1930 1930
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1929 1929
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1920 120 (:LINEAR RTL::LOGAND-BND))
 (1744 610 (:REWRITE DEFAULT-MINUS))
 (1497 1497 (:REWRITE THE-FLOOR-BELOW))
 (1497 1497 (:REWRITE THE-FLOOR-ABOVE))
 (1481 1481
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1481 1481
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1458 243 (:REWRITE |(- (+ x y))|))
 (1408 1408
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1408 1408 (:REWRITE INTEGERP-<-CONSTANT))
 (1408 1408 (:REWRITE CONSTANT-<-INTEGERP))
 (1408 1408
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1408 1408
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1408 1408
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1408 1408
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1408 1408 (:REWRITE |(< c (- x))|))
 (1408 1408
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1408 1408
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1408 1408
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1408 1408
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1408 1408 (:REWRITE |(< (/ x) (/ y))|))
 (1408 1408 (:REWRITE |(< (- x) c)|))
 (1408 1408 (:REWRITE |(< (- x) (- y))|))
 (1300 79
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1300 79
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1300 79
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1288 42 (:REWRITE RTL::NEG-BITN-1))
 (1164 79 (:REWRITE MOD-CANCEL-*-CONST))
 (1132 4 (:REWRITE RTL::LOGAND-BVECP))
 (1127 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1072 1072
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1059 1059
       (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (1056 1056
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (1041 1041
       (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (1041 1041 (:TYPE-PRESCRIPTION NATP))
 (1032 12 (:LINEAR MOD-BOUNDS-3))
 (993 483 (:REWRITE NORMALIZE-ADDENDS))
 (960 60 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (960 60 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (930 60 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (930 60 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (901 901
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (877 877
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (874 874 (:REWRITE DEFAULT-EXPT-2))
 (874 874 (:REWRITE DEFAULT-EXPT-1))
 (874 874 (:REWRITE |(expt 1/c n)|))
 (874 874 (:REWRITE |(expt (- x) n)|))
 (855 110
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (844 14 (:REWRITE |(< (logand x y) 0)|))
 (790 79 (:REWRITE DEFAULT-MOD-2))
 (704 354 (:REWRITE DEFAULT-TIMES-1))
 (596 24 (:LINEAR MOD-BOUNDS-2))
 (517 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (490 490 (:REWRITE |(< (/ x) 0)|))
 (490 490 (:REWRITE |(< (* x y) 0)|))
 (476 476
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (476 476
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (468 468
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (416 416
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (416 416
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (416 416 (:REWRITE |(< 0 (/ x))|))
 (416 416 (:REWRITE |(< 0 (* x y))|))
 (408 24 (:REWRITE |(* y x)|))
 (334 334
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (334 334
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (334 334
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (279 9 (:LINEAR RTL::MOD-BND-2))
 (254 17 (:REWRITE |(+ y x)|))
 (224 110
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (201 25 (:REWRITE DEFAULT-LOGAND-2))
 (201 25 (:REWRITE DEFAULT-LOGAND-1))
 (193 193 (:REWRITE REDUCE-INTEGERP-+))
 (193 193 (:REWRITE INTEGERP-MINUS-X))
 (193 193 (:META META-INTEGERP-CORRECT))
 (167 167 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (167 167 (:LINEAR EXPT-LINEAR-UPPER-<))
 (167 167 (:LINEAR EXPT-LINEAR-LOWER-<))
 (167 167 (:LINEAR EXPT->=-1-TWO))
 (167 167 (:LINEAR EXPT->-1-TWO))
 (167 167 (:LINEAR EXPT-<=-1-ONE))
 (167 167 (:LINEAR EXPT-<-1-TWO))
 (167 167 (:LINEAR EXPT-<-1-ONE))
 (152 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (150 109 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (135 1 (:REWRITE MOD-ZERO . 1))
 (119 110 (:REWRITE |(equal (- x) c)|))
 (119 110 (:REWRITE |(equal (- x) (- y))|))
 (115 79 (:REWRITE DEFAULT-MOD-1))
 (110 110
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (110 110
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (110 110
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (110 110 (:REWRITE |(equal c (/ x))|))
 (110 110 (:REWRITE |(equal c (- x))|))
 (110 110 (:REWRITE |(equal (/ x) c)|))
 (110 110 (:REWRITE |(equal (/ x) (/ y))|))
 (88 88
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (86 1 (:REWRITE |(/ (* x y))|))
 (80 80 (:REWRITE |(< (+ c/d x) y)|))
 (79 79
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (79 79 (:REWRITE |(mod x (- y))| . 3))
 (79 79 (:REWRITE |(mod x (- y))| . 2))
 (79 79 (:REWRITE |(mod x (- y))| . 1))
 (79 79
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (79 79 (:REWRITE |(mod (- x) y)| . 3))
 (79 79 (:REWRITE |(mod (- x) y)| . 2))
 (79 79 (:REWRITE |(mod (- x) y)| . 1))
 (79 79
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (79 79 (:REWRITE |(- (* c x))|))
 (77 77 (:REWRITE |(< x (+ c/d y))|))
 (42 42 (:REWRITE RTL::BITN-NEG))
 (34 1 (:REWRITE |(* (/ c) (expt d n))|))
 (33 1 (:REWRITE MOD-ZERO . 2))
 (28 14 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (25 25 (:REWRITE |arith (expt x c)|))
 (25 25 (:REWRITE LOGAND-CONSTANT-MASK))
 (24 24 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (18 18 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (18 18 (:REWRITE RTL::BITS-NEG-INDICES))
 (15 15 (:REWRITE |(+ x (- x))|))
 (14 14 (:REWRITE |arith (expt 1/c n)|))
 (14 1
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (13 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (11 11
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (9 9 (:LINEAR RTL::MOD-BND-3))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 1 (:REWRITE |(* x (- y))|))
 (3 3 (:REWRITE |arith (+ c (+ d x))|))
 (2 2 (:REWRITE MOD-NEGATIVE . 3))
 (2 2 (:REWRITE MOD-NEGATIVE . 2))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|)))
(RTL::LEMMA1 (1118 44 (:REWRITE RTL::BITS-TAIL-GEN))
             (637 603 (:REWRITE DEFAULT-+-2))
             (627 603 (:REWRITE DEFAULT-+-1))
             (510 170 (:REWRITE DEFAULT-*-2))
             (406 268 (:REWRITE DEFAULT-<-2))
             (312 268 (:REWRITE DEFAULT-<-1))
             (170 170 (:REWRITE DEFAULT-*-1))
             (148 90 (:REWRITE RTL::BITS-REVERSE-INDICES))
             (90 90 (:REWRITE RTL::BITS-NEG-INDICES))
             (57 57 (:REWRITE ZIP-OPEN))
             (30 30 (:REWRITE DEFAULT-UNARY-MINUS)))
(RTL::LEMMA2
 (1600
  1600
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1600
      1600
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1600
     1600
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1600 1600
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1600 1600
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (692 7 (:REWRITE MOD-ZERO . 3))
 (516 97
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (414 15 (:REWRITE ODD-EXPT-THM))
 (399 112 (:REWRITE DEFAULT-PLUS-2))
 (398 7 (:REWRITE DEFAULT-MOD-RATIO))
 (334 9 (:LINEAR EXPT-X->=-X))
 (334 9 (:LINEAR EXPT-X->-X))
 (324 7 (:REWRITE MOD-X-Y-=-X . 4))
 (311 85 (:REWRITE SIMPLIFY-SUMS-<))
 (283 85
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (283 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (276 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (268 97 (:REWRITE DEFAULT-LESS-THAN-2))
 (265 85
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (256 1 (:REWRITE CANCEL-MOD-+))
 (247 31 (:REWRITE DEFAULT-TIMES-2))
 (207 112 (:REWRITE DEFAULT-PLUS-1))
 (204 7 (:REWRITE MOD-ZERO . 4))
 (184 6 (:REWRITE |(* y x)|))
 (175 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (175 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (175 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (160 16 (:REWRITE DEFAULT-DIVIDE))
 (159 9 (:LINEAR EXPT-<=-1-TWO))
 (158 2 (:REWRITE |(* x (+ y z))|))
 (142 97 (:REWRITE DEFAULT-LESS-THAN-1))
 (134 1 (:REWRITE RTL::BITS-TAIL))
 (129 57 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (98 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (97 97 (:REWRITE THE-FLOOR-BELOW))
 (97 97 (:REWRITE THE-FLOOR-ABOVE))
 (97 97
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (97 97
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (96 16 (:REWRITE |(/ (expt x n))|))
 (86 31 (:REWRITE DEFAULT-TIMES-1))
 (86 2 (:REWRITE |(integerp (- x))|))
 (85 85 (:REWRITE INTEGERP-<-CONSTANT))
 (85 85 (:REWRITE CONSTANT-<-INTEGERP))
 (85 85
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (85 85
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (85 85
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (85 85
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (85 85 (:REWRITE |(< c (- x))|))
 (85 85
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (85 85
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (85 85
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (85 85
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (85 85 (:REWRITE |(< (/ x) (/ y))|))
 (85 85 (:REWRITE |(< (- x) c)|))
 (85 85 (:REWRITE |(< (- x) (- y))|))
 (70 7 (:REWRITE DEFAULT-MOD-2))
 (68 68 (:REWRITE DEFAULT-EXPT-2))
 (68 68 (:REWRITE DEFAULT-EXPT-1))
 (68 68 (:REWRITE |(expt 1/c n)|))
 (68 68 (:REWRITE |(expt (- x) n)|))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (66 66
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (66 66
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (56 2 (:REWRITE |(* (- x) y)|))
 (56 1
     (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (54 19 (:REWRITE DEFAULT-MINUS))
 (47 47
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (44 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (41 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (41 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (38 38 (:REWRITE |(< 0 (/ x))|))
 (38 38 (:REWRITE |(< 0 (* x y))|))
 (34 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (34 1
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (27 18 (:REWRITE |(equal (- x) (- y))|))
 (25 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (25 1 (:REWRITE MOD-X-Y-=-X . 2))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (18 18 (:REWRITE |(equal c (/ x))|))
 (18 18 (:REWRITE |(equal c (- x))|))
 (18 18 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(equal (/ x) (/ y))|))
 (18 18 (:REWRITE |(equal (- x) c)|))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (16 1
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE MOD-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:LINEAR EXPT->=-1-TWO))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<=-1-ONE))
 (9 9 (:LINEAR EXPT-<-1-TWO))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:REWRITE |arith (expt x c)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 7 (:REWRITE DEFAULT-MOD-1))
 (5 5 (:REWRITE |arith (expt 1/c n)|))
 (5 5 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (2 2
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (2 2 (:REWRITE |(- (* c x))|))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|)))
(RTL::GEN-EXTEND-3 (404 16 (:DEFINITION EXPT))
                   (260 5 (:REWRITE RTL::BITS-TAIL-GEN))
                   (211 178 (:REWRITE DEFAULT-+-2))
                   (187 178 (:REWRITE DEFAULT-+-1))
                   (157 147 (:REWRITE DEFAULT-<-2))
                   (157 147 (:REWRITE DEFAULT-<-1))
                   (104 40 (:REWRITE DEFAULT-*-2))
                   (51 25 (:REWRITE RTL::BITS-REVERSE-INDICES))
                   (45 5 (:REWRITE RTL::BITS-TAIL))
                   (40 40 (:REWRITE DEFAULT-*-1))
                   (35 25 (:REWRITE RTL::BITS-NEG-INDICES))
                   (16 16 (:REWRITE ZIP-OPEN))
                   (12 12 (:REWRITE DEFAULT-UNARY-MINUS)))
(RTL::LEMMA1
 (2316 22 (:REWRITE MOD-ZERO . 3))
 (2157
  2157
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2157
      2157
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2157
     2157
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2157 2157
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2157 2157
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1424 22 (:REWRITE DEFAULT-MOD-RATIO))
 (988 22 (:REWRITE MOD-X-Y-=-X . 4))
 (966 4 (:REWRITE CANCEL-MOD-+))
 (954 22 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (882 216 (:REWRITE DEFAULT-PLUS-2))
 (870 114 (:REWRITE DEFAULT-TIMES-2))
 (830 26 (:REWRITE |(* y x)|))
 (726 10 (:REWRITE |(* x (+ y z))|))
 (636 53 (:REWRITE |(/ (expt x n))|))
 (628 22 (:REWRITE MOD-ZERO . 4))
 (609 216 (:REWRITE DEFAULT-PLUS-1))
 (550 22 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (550 22 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (550 22 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (530 53 (:REWRITE DEFAULT-DIVIDE))
 (410 82
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (368 114 (:REWRITE DEFAULT-TIMES-1))
 (335 83 (:REWRITE DEFAULT-LESS-THAN-2))
 (325 73
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (318 53 (:REWRITE |(- (+ x y))|))
 (306 72 (:REWRITE SIMPLIFY-SUMS-<))
 (305 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (248 8 (:REWRITE |(integerp (- x))|))
 (246 120 (:REWRITE DEFAULT-MINUS))
 (220 22 (:REWRITE DEFAULT-MOD-2))
 (218 74
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (212 212
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (193 9 (:REWRITE |(* (- x) y)|))
 (151 34
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (145 145
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (136 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (136 4
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (128 83 (:REWRITE DEFAULT-LESS-THAN-1))
 (121 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (111 57 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (102 1 (:REWRITE RTL::BITS-TAIL))
 (100 100 (:REWRITE DEFAULT-EXPT-2))
 (100 100 (:REWRITE DEFAULT-EXPT-1))
 (100 100 (:REWRITE |(expt 1/c n)|))
 (100 100 (:REWRITE |(expt (- x) n)|))
 (100 4 (:REWRITE MOD-X-Y-=-X . 2))
 (93 44 (:META META-INTEGERP-CORRECT))
 (83 83 (:REWRITE THE-FLOOR-BELOW))
 (83 83 (:REWRITE THE-FLOOR-ABOVE))
 (83 74 (:REWRITE |(< (- x) (- y))|))
 (82 82
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (82 82
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (74 74 (:REWRITE INTEGERP-<-CONSTANT))
 (74 74 (:REWRITE CONSTANT-<-INTEGERP))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< c (- x))|))
 (74 74
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (74 74
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< (/ x) (/ y))|))
 (74 74 (:REWRITE |(< (- x) c)|))
 (66 27 (:REWRITE ODD-EXPT-THM))
 (64 4
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (64 4
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (64 4
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (62 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (61 34 (:REWRITE |(equal (- x) c)|))
 (61 34 (:REWRITE |(equal (- x) (- y))|))
 (44 44 (:REWRITE REDUCE-INTEGERP-+))
 (44 44 (:REWRITE INTEGERP-MINUS-X))
 (38 8 (:LINEAR EXPT-<=-1-TWO))
 (34 34
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (34 34
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (34 34
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (34 34 (:REWRITE |(equal c (/ x))|))
 (34 34 (:REWRITE |(equal c (- x))|))
 (34 34 (:REWRITE |(equal (/ x) c)|))
 (34 34 (:REWRITE |(equal (/ x) (/ y))|))
 (34 4 (:REWRITE MOD-CANCEL-*-CONST))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< 0 (/ x))|))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (29 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (22 22 (:REWRITE FOLD-CONSTS-IN-+))
 (22 22 (:REWRITE DEFAULT-MOD-1))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (21 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:REWRITE |(equal (+ (- c) x) y)|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (11 1 (:REWRITE |(* -1 x)|))
 (10 10 (:REWRITE |arith (expt x c)|))
 (10 10 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (8 8 (:REWRITE |(- (* c x))|))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-TWO))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE |(equal (expt 2 n) c)|))
 (5 5 (:REWRITE |arith (expt 1/c n)|))
 (5 5
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (4 4
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE |(mod x (- y))| . 3))
 (4 4 (:REWRITE |(mod x (- y))| . 2))
 (4 4 (:REWRITE |(mod x (- y))| . 1))
 (4 4
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (4 4 (:REWRITE |(mod (- x) y)| . 3))
 (4 4 (:REWRITE |(mod (- x) y)| . 2))
 (4 4 (:REWRITE |(mod (- x) y)| . 1))
 (4 4
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3 3
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (3 3
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |arith (+ c (+ d x))|))
 (1 1
    (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::LEMMA2
 (409 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (116 1 (:REWRITE DEFAULT-MOD-RATIO))
 (92 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (62 6 (:REWRITE SIMPLIFY-SUMS-<))
 (61 37 (:REWRITE DEFAULT-PLUS-1))
 (60
  60
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (60 60
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (60 60
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (60 60
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (60 60
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (58 5 (:REWRITE |(+ y (+ x z))|))
 (57 2
     (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
 (55 37 (:REWRITE DEFAULT-PLUS-2))
 (50 2 (:REWRITE ODD-EXPT-THM))
 (42 6 (:REWRITE DEFAULT-TIMES-2))
 (40 1
     (:REWRITE |(* (expt c m) (expt d n))|))
 (28 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (26 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (26 6 (:REWRITE DEFAULT-TIMES-1))
 (25 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (12 3 (:REWRITE DEFAULT-MINUS))
 (12 1 (:REWRITE |(/ (expt x n))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 1 (:REWRITE DEFAULT-MOD-2))
 (10 1 (:REWRITE DEFAULT-MOD-1))
 (10 1 (:REWRITE DEFAULT-DIVIDE))
 (10 1 (:REWRITE |(* c (expt d n))|))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (7 1 (:REWRITE RTL::BITS-TAIL))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 1 (:REWRITE |(- (+ x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-TWO))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2 2
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(+ 0 x)|))
 (2 2 (:REWRITE |(* 1 x)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::TOP-THM-1
 (5350 22 (:REWRITE RTL::BITS-TAIL-GEN))
 (671 21 (:LINEAR EXPT-X->=-X))
 (671 21 (:LINEAR EXPT-X->-X))
 (530 120
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (501 21 (:LINEAR EXPT-<=-1-TWO))
 (448
  448
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (448 448
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (448
     448
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (448 448
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (448 448
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (398 187 (:REWRITE DEFAULT-PLUS-2))
 (354 22 (:REWRITE ODD-EXPT-THM))
 (318 120 (:REWRITE DEFAULT-LESS-THAN-2))
 (315 109 (:REWRITE SIMPLIFY-SUMS-<))
 (315 109
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (315 109
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (287 187 (:REWRITE DEFAULT-PLUS-1))
 (250 42
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (229 21 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (166 22 (:REWRITE RTL::BITS-TAIL))
 (128 120 (:REWRITE DEFAULT-LESS-THAN-1))
 (120 120 (:REWRITE THE-FLOOR-BELOW))
 (120 120 (:REWRITE THE-FLOOR-ABOVE))
 (120 120
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (120 120
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (110 110
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (110 110 (:REWRITE INTEGERP-<-CONSTANT))
 (110 110 (:REWRITE CONSTANT-<-INTEGERP))
 (110 110
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (110 110
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (110 110
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (110 110
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (110 110 (:REWRITE |(< c (- x))|))
 (110 110
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (110 110
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (110 110
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (110 110
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (110 110 (:REWRITE |(< (/ x) (/ y))|))
 (110 110 (:REWRITE |(< (- x) c)|))
 (110 110 (:REWRITE |(< (- x) (- y))|))
 (102 102
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (100 13
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (97 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (89 89 (:REWRITE DEFAULT-EXPT-2))
 (89 89 (:REWRITE DEFAULT-EXPT-1))
 (89 89 (:REWRITE |(expt 1/c n)|))
 (89 89 (:REWRITE |(expt (- x) n)|))
 (53 53
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (53 53
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (53 53 (:REWRITE |(< 0 (/ x))|))
 (53 53 (:REWRITE |(< 0 (* x y))|))
 (47 7 (:REWRITE DEFAULT-MINUS))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (42 42
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (42 42
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 14 (:REWRITE |(equal (- x) (- y))|))
 (22 22 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (22 22 (:REWRITE RTL::BITS-NEG-INDICES))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<))
 (21 21 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 21 (:LINEAR EXPT->=-1-TWO))
 (21 21 (:LINEAR EXPT->-1-TWO))
 (21 21 (:LINEAR EXPT-<=-1-ONE))
 (21 21 (:LINEAR EXPT-<-1-TWO))
 (21 21 (:LINEAR EXPT-<-1-ONE))
 (20 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (12 4 (:REWRITE RTL::LOGXOR-BVECP))
 (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE DEFAULT-LOGXOR-2))
 (4 4 (:REWRITE DEFAULT-LOGXOR-1))
 (4 2 (:REWRITE DEFAULT-LOGNOT))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|)))
(RTL::LEMMA-SUM=0
 (14776 48 (:REWRITE RTL::BITS-TAIL-GEN))
 (6004 510
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3376 14 (:REWRITE RTL::NEG-BITN-0))
 (2210 64 (:LINEAR EXPT-X->=-X))
 (2210 64 (:LINEAR EXPT-X->-X))
 (1663 64 (:LINEAR EXPT-<=-1-TWO))
 (1268
  1268
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1268
      1268
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1268
     1268
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1268 1268
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1268 1268
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1185 510 (:REWRITE DEFAULT-LESS-THAN-2))
 (1104 61 (:REWRITE ODD-EXPT-THM))
 (1022 329 (:REWRITE SIMPLIFY-SUMS-<))
 (1022 329
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (968 329
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (916 256 (:REWRITE |(+ c (+ d x))|))
 (671 599 (:REWRITE DEFAULT-PLUS-2))
 (645 599 (:REWRITE DEFAULT-PLUS-1))
 (528 510 (:REWRITE DEFAULT-LESS-THAN-1))
 (510 510 (:REWRITE THE-FLOOR-BELOW))
 (510 510 (:REWRITE THE-FLOOR-ABOVE))
 (510 510
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (510 510
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (420 14 (:REWRITE RTL::NEG-BITN-1))
 (414 48 (:REWRITE RTL::BITS-TAIL))
 (353 329
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (329 329 (:REWRITE INTEGERP-<-CONSTANT))
 (329 329 (:REWRITE CONSTANT-<-INTEGERP))
 (329 329
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (329 329
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (329 329
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (329 329
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (329 329 (:REWRITE |(< c (- x))|))
 (329 329
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (329 329
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (329 329
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (329 329
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (329 329 (:REWRITE |(< (/ x) (/ y))|))
 (329 329 (:REWRITE |(< (- x) c)|))
 (329 329 (:REWRITE |(< (- x) (- y))|))
 (219 219 (:REWRITE DEFAULT-EXPT-2))
 (219 219 (:REWRITE DEFAULT-EXPT-1))
 (219 219 (:REWRITE |(expt 1/c n)|))
 (219 219 (:REWRITE |(expt (- x) n)|))
 (181 181 (:REWRITE |(< x (+ c/d y))|))
 (140 14 (:REWRITE DEFAULT-MINUS))
 (130 130
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (130 130 (:REWRITE NORMALIZE-ADDENDS))
 (130 86 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (128 128
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (128 128
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (128 128
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (111 111 (:REWRITE |(< 0 (* x y))|))
 (64 64 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (64 64 (:LINEAR EXPT-LINEAR-UPPER-<))
 (64 64 (:LINEAR EXPT-LINEAR-LOWER-<))
 (64 64 (:LINEAR EXPT->=-1-TWO))
 (64 64 (:LINEAR EXPT->-1-TWO))
 (64 64 (:LINEAR EXPT-<=-1-ONE))
 (64 64 (:LINEAR EXPT-<-1-TWO))
 (64 64 (:LINEAR EXPT-<-1-ONE))
 (59 29
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (56 10 (:REWRITE DEFAULT-TIMES-2))
 (56 10 (:REWRITE DEFAULT-TIMES-1))
 (55 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (48 48 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (48 48 (:REWRITE RTL::BITS-NEG-INDICES))
 (42 14 (:REWRITE RTL::BVECP-BITN-0))
 (41 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (36 36 (:REWRITE FOLD-CONSTS-IN-+))
 (36 2 (:REWRITE DEFAULT-LOGXOR-2))
 (35 35 (:REWRITE |(< (+ c/d x) y)|))
 (35 35 (:REWRITE |(< (+ (- c) x) y)|))
 (29 29
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (29 29
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (29 29
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (29 29 (:REWRITE |(equal c (/ x))|))
 (29 29 (:REWRITE |(equal c (- x))|))
 (29 29 (:REWRITE |(equal (/ x) c)|))
 (29 29 (:REWRITE |(equal (/ x) (/ y))|))
 (29 29 (:REWRITE |(equal (- x) c)|))
 (29 29 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (14 14 (:REWRITE RTL::BITN-NEG))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (4 2 (:REWRITE DEFAULT-LOGXOR-1))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::LEMMA-LOGXOR=0
 (13337 34 (:REWRITE RTL::NEG-BITN-0))
 (3401 26 (:REWRITE RTL::BITS-TAIL-GEN))
 (2044 120
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (1774 279
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1594 60 (:LINEAR EXPT-X->-X))
 (1360 60 (:LINEAR EXPT-X->=-X))
 (1301
  1301
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1301
      1301
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1301
     1301
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1301 1301
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1301 1301
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1204 60 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1056 60 (:LINEAR EXPT->-1-ONE))
 (1020 34 (:REWRITE RTL::NEG-BITN-1))
 (840 60 (:LINEAR EXPT->=-1-ONE))
 (819 279 (:REWRITE DEFAULT-LESS-THAN-2))
 (796 230 (:REWRITE SIMPLIFY-SUMS-<))
 (796 230
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (749 26 (:REWRITE ODD-EXPT-THM))
 (661 230
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (458 120
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (441 441 (:REWRITE DEFAULT-EXPT-2))
 (441 441 (:REWRITE DEFAULT-EXPT-1))
 (441 441 (:REWRITE |(expt 1/c n)|))
 (441 441 (:REWRITE |(expt (- x) n)|))
 (388 60 (:LINEAR EXPT-<=-1-TWO))
 (340 34 (:REWRITE DEFAULT-MINUS))
 (305 279 (:REWRITE DEFAULT-LESS-THAN-1))
 (294 26 (:REWRITE RTL::BITS-TAIL))
 (279 279 (:REWRITE THE-FLOOR-BELOW))
 (279 279 (:REWRITE THE-FLOOR-ABOVE))
 (279 279
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (279 279
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (264 66 (:REWRITE |(+ c (+ d x))|))
 (230 230
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (230 230 (:REWRITE INTEGERP-<-CONSTANT))
 (230 230 (:REWRITE CONSTANT-<-INTEGERP))
 (230 230
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (230 230
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (230 230
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (230 230
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (230 230 (:REWRITE |(< c (- x))|))
 (230 230
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (230 230
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (230 230
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (230 230
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (230 230 (:REWRITE |(< (/ x) (/ y))|))
 (230 230 (:REWRITE |(< (- x) c)|))
 (230 230 (:REWRITE |(< (- x) (- y))|))
 (215 196 (:REWRITE DEFAULT-PLUS-2))
 (215 196 (:REWRITE DEFAULT-PLUS-1))
 (120 120
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (120 120
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (118 56 (:REWRITE DEFAULT-LOGXOR-2))
 (102 34 (:REWRITE RTL::BVECP-BITN-0))
 (100 18 (:REWRITE DEFAULT-TIMES-2))
 (100 18 (:REWRITE DEFAULT-TIMES-1))
 (98 55
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (90 55
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (78 26 (:REWRITE RTL::LOGXOR-BVECP))
 (67 55 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (60 60 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (60 60 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (60 60 (:LINEAR EXPT-LINEAR-UPPER-<))
 (60 60 (:LINEAR EXPT-LINEAR-LOWER-<))
 (60 60 (:LINEAR EXPT->=-1-TWO))
 (60 60 (:LINEAR EXPT->-1-TWO))
 (60 60 (:LINEAR EXPT-<=-1-ONE))
 (60 60 (:LINEAR EXPT-<-1-TWO))
 (60 60 (:LINEAR EXPT-<-1-ONE))
 (58 58 (:REWRITE |(< x (+ c/d y))|))
 (58 56 (:REWRITE DEFAULT-LOGXOR-1))
 (55 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (55 55
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (55 55
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (55 55 (:REWRITE |(equal c (/ x))|))
 (55 55 (:REWRITE |(equal c (- x))|))
 (55 55 (:REWRITE |(equal (/ x) c)|))
 (55 55 (:REWRITE |(equal (/ x) (/ y))|))
 (55 55 (:REWRITE |(equal (- x) c)|))
 (55 55 (:REWRITE |(equal (- x) (- y))|))
 (43 43
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (43 43
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (43 43
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (43 43 (:REWRITE NORMALIZE-ADDENDS))
 (43 43 (:REWRITE |(< (/ x) 0)|))
 (43 43 (:REWRITE |(< (* x y) 0)|))
 (41 41 (:REWRITE |(< 0 (* x y))|))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (34 34 (:REWRITE RTL::BITN-NEG))
 (32 32 (:REWRITE REDUCE-INTEGERP-+))
 (32 32 (:REWRITE INTEGERP-MINUS-X))
 (32 32 (:META META-INTEGERP-CORRECT))
 (29 28 (:REWRITE DEFAULT-LOGIOR-2))
 (29 28 (:REWRITE DEFAULT-LOGIOR-1))
 (26 26 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (26 26 (:REWRITE RTL::BITS-NEG-INDICES))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (3 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE RTL::BITN-CAT-CONSTANTS))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::LEMMA-CARRY
 (43288 204 (:REWRITE RTL::BITS-TAIL-GEN))
 (15428 1388
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9324
  9324
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9324
      9324
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9324
     9324
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9324 9324
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9324 9324
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5965 44 (:REWRITE RTL::NEG-BITN-0))
 (4308 1392 (:REWRITE DEFAULT-LESS-THAN-2))
 (4002 148 (:LINEAR EXPT-<=-1-TWO))
 (3944 926 (:REWRITE SIMPLIFY-SUMS-<))
 (3944 926
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3917 926
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3908 280 (:REWRITE ODD-EXPT-THM))
 (1999 1540 (:REWRITE DEFAULT-PLUS-2))
 (1777 1540 (:REWRITE DEFAULT-PLUS-1))
 (1626 1392 (:REWRITE DEFAULT-LESS-THAN-1))
 (1568 204 (:REWRITE RTL::BITS-TAIL))
 (1493 926
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1392 1392 (:REWRITE THE-FLOOR-BELOW))
 (1392 1392 (:REWRITE THE-FLOOR-ABOVE))
 (1388 1388
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1388 1388
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1320 44 (:REWRITE RTL::NEG-BITN-1))
 (926 926 (:REWRITE INTEGERP-<-CONSTANT))
 (926 926 (:REWRITE CONSTANT-<-INTEGERP))
 (926 926
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (926 926
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (926 926
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (926 926
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (926 926 (:REWRITE |(< c (- x))|))
 (926 926
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (926 926
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (926 926
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (926 926
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (926 926 (:REWRITE |(< (/ x) (/ y))|))
 (926 926 (:REWRITE |(< (- x) c)|))
 (926 926 (:REWRITE |(< (- x) (- y))|))
 (658 658 (:REWRITE DEFAULT-EXPT-2))
 (658 658 (:REWRITE DEFAULT-EXPT-1))
 (658 658 (:REWRITE |(expt 1/c n)|))
 (658 658 (:REWRITE |(expt (- x) n)|))
 (462 462 (:REWRITE |(< x (+ c/d y))|))
 (440 44 (:REWRITE DEFAULT-MINUS))
 (408 288 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (377 80
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (377 80
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (346 346
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (346 346 (:REWRITE NORMALIZE-ADDENDS))
 (338 80 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (296 296 (:REWRITE |(< 0 (* x y))|))
 (296 296
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (296 296
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (296 296
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (204 204
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (204 204 (:REWRITE RTL::BITS-NEG-INDICES))
 (156 28 (:REWRITE DEFAULT-TIMES-2))
 (156 28 (:REWRITE DEFAULT-TIMES-1))
 (148 148 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (148 148 (:LINEAR EXPT-LINEAR-UPPER-<))
 (148 148 (:LINEAR EXPT-LINEAR-LOWER-<))
 (148 148 (:LINEAR EXPT->=-1-TWO))
 (148 148 (:LINEAR EXPT->-1-TWO))
 (148 148 (:LINEAR EXPT-<=-1-ONE))
 (148 148 (:LINEAR EXPT-<-1-TWO))
 (148 148 (:LINEAR EXPT-<-1-ONE))
 (132 44 (:REWRITE RTL::BVECP-BITN-0))
 (80 80
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (80 80
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (80 80
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (80 80 (:REWRITE |(equal c (/ x))|))
 (80 80 (:REWRITE |(equal c (- x))|))
 (80 80 (:REWRITE |(equal (/ x) c)|))
 (80 80 (:REWRITE |(equal (/ x) (/ y))|))
 (80 80 (:REWRITE |(equal (- x) c)|))
 (80 80 (:REWRITE |(equal (- x) (- y))|))
 (66 66 (:REWRITE REDUCE-INTEGERP-+))
 (66 66 (:REWRITE INTEGERP-MINUS-X))
 (66 66 (:META META-INTEGERP-CORRECT))
 (54 54 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (46 46 (:REWRITE |(< (/ x) 0)|))
 (46 46 (:REWRITE |(< (* x y) 0)|))
 (44 44 (:REWRITE RTL::BITN-NEG))
 (40 40 (:REWRITE |(< (+ c/d x) y)|))
 (40 40 (:REWRITE |(< (+ (- c) x) y)|))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (34 34 (:REWRITE |arith (expt x c)|))
 (28 28 (:REWRITE |arith (expt 1/c n)|))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (22 22 (:REWRITE |(< 0 (/ x))|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:REWRITE |arith (+ c (+ d x))|))
 (6 6
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::LEMMA (25957 745 (:REWRITE RTL::BITS-TAIL-GEN))
            (15435 543 (:REWRITE RTL::NEG-BITN-0))
            (9077 7967 (:REWRITE DEFAULT-+-2))
            (8718 2906 (:REWRITE DEFAULT-*-2))
            (8469 7967 (:REWRITE DEFAULT-+-1))
            (7139 4487 (:REWRITE DEFAULT-<-2))
            (5287 745 (:REWRITE RTL::BITS-TAIL))
            (5226 4487 (:REWRITE DEFAULT-<-1))
            (2906 2906 (:REWRITE DEFAULT-*-1))
            (1421 543 (:REWRITE RTL::BVECP-BITN-0))
            (1393 543 (:REWRITE RTL::NEG-BITN-1))
            (1306 1306 (:REWRITE ZIP-OPEN))
            (1142 381 (:REWRITE DEFAULT-UNARY-MINUS))
            (745 745 (:REWRITE RTL::BITS-NEG-INDICES))
            (539 539 (:REWRITE RTL::BITN-NEG))
            (450 150 (:REWRITE RTL::LOGXOR-BVECP))
            (88 88 (:REWRITE ZP-OPEN))
            (4 4 (:REWRITE RTL::BITN-CAT-CONSTANTS)))
(RTL::TOP-THM-2 (174 6 (:REWRITE RTL::NEG-BITN-0))
                (114 6 (:REWRITE RTL::BITS-TAIL-GEN))
                (59 35 (:REWRITE DEFAULT-<-2))
                (52 42 (:REWRITE DEFAULT-+-2))
                (48 42 (:REWRITE DEFAULT-+-1))
                (41 35 (:REWRITE DEFAULT-<-1))
                (39 13 (:REWRITE DEFAULT-*-2))
                (36 6 (:REWRITE RTL::BITS-TAIL))
                (18 6 (:REWRITE RTL::NEG-BITN-1))
                (18 6 (:REWRITE DEFAULT-UNARY-MINUS))
                (18 6 (:REWRITE RTL::BVECP-BITN-0))
                (13 13 (:REWRITE DEFAULT-*-1))
                (12 12 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
                (11 11 (:REWRITE ZIP-OPEN))
                (6 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
                (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
                (6 6 (:REWRITE RTL::BITN-NEG))
                (6 2 (:REWRITE RTL::LOGXOR-BVECP))
                (4 4
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
