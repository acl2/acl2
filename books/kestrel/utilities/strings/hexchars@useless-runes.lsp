(UBYTE8=>HEXCHARS)
(HEX-DIGIT-CHAR-P-OF-UBYTE8=>HEXCHARS.HI-CHAR
 (48 3
     (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (14 10 (:REWRITE DEFAULT-+-2))
 (12 11 (:REWRITE DEFAULT-*-2))
 (12 11 (:REWRITE DEFAULT-*-1))
 (12 4
     (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-NONZERO-HEX-DIGIT-CHAR-P))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 3 (:REWRITE COMMUTATIVITY-OF-+))
 (9 3 (:DEFINITION NFIX))
 (8 8
    (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGIT-CHAR-P$INLINE))
 (8
  8
  (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-CHAR-LISTP))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:DEFINITION IFIX)))
(HEX-DIGIT-CHAR-P-OF-UBYTE8=>HEXCHARS.LO-CHAR
 (48 3
     (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (17 12 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (15 13 (:REWRITE DEFAULT-*-2))
 (14 13 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 4
     (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-NONZERO-HEX-DIGIT-CHAR-P))
 (9 3 (:REWRITE COMMUTATIVITY-OF-+))
 (9 3 (:DEFINITION NFIX))
 (8 8
    (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGIT-CHAR-P$INLINE))
 (8
  8
  (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-CHAR-LISTP))
 (8 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:DEFINITION IFIX)))
(UBYTE8=>HEXCHARS
     (870 870
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (870 870
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (870 870
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (590 10 (:REWRITE DEFAULT-PLUS-1))
     (588 10 (:REWRITE DEFAULT-PLUS-2))
     (221 17 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (192 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (153 17
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (153 17
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (153 17
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (106 2 (:REWRITE CANCEL-MOD-+))
     (85 17 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (85 17 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (85 17 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (85 17
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (81 12 (:REWRITE INTEGERP-MINUS-X))
     (70 2 (:REWRITE MOD-X-Y-=-X . 4))
     (68 1 (:REWRITE FLOOR-ZERO . 3))
     (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (65 13
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (65 13
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (62 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (60 2 (:REWRITE MOD-X-Y-=-X . 3))
     (59 19 (:REWRITE DEFAULT-LESS-THAN-1))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (57 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (57 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (53 1 (:REWRITE CANCEL-FLOOR-+))
     (51 6 (:REWRITE |(* (- x) y)|))
     (44 2 (:REWRITE MOD-ZERO . 3))
     (37 37 (:REWRITE DEFAULT-TIMES-2))
     (37 37 (:REWRITE DEFAULT-TIMES-1))
     (36 2 (:REWRITE MOD-ZERO . 4))
     (35 1 (:REWRITE FLOOR-ZERO . 5))
     (31 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (30 6 (:REWRITE DEFAULT-MINUS))
     (30 1 (:REWRITE FLOOR-ZERO . 4))
     (27 6 (:REWRITE |(- (* c x))|))
     (22 22 (:REWRITE THE-FLOOR-BELOW))
     (22 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (22 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (22 2 (:REWRITE DEFAULT-MOD-RATIO))
     (22 1 (:REWRITE FLOOR-=-X/Y . 3))
     (22 1 (:REWRITE FLOOR-=-X/Y . 2))
     (22 1 (:LINEAR MOD-BOUNDS-3))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (19 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19 (:REWRITE INTEGERP-<-CONSTANT))
     (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
     (19 19 (:REWRITE CONSTANT-<-INTEGERP))
     (19 19
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (19 19
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (19 19
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (19 19
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (19 19 (:REWRITE |(< c (- x))|))
     (19 19
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (19 19
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (19 19
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (19 19
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (19 19 (:REWRITE |(< (/ x) (/ y))|))
     (19 19 (:REWRITE |(< (- x) c)|))
     (19 19 (:REWRITE |(< (- x) (- y))|))
     (17 17 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (13 13 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (13 13
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (13 13 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (13 13
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (13 13 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (10 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (10 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (10 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (10 2 (:REWRITE MOD-X-Y-=-X . 2))
     (10 2
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (10 2 (:REWRITE MOD-CANCEL-*-CONST))
     (10 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (10 2
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (10 2
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:META META-INTEGERP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (5 1 (:REWRITE FLOOR-ZERO . 2))
     (5 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (5 1
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 1
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE DEFAULT-MOD-1))
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
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2))
     (1 1
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(floor x (- y))| . 2))
     (1 1 (:REWRITE |(floor x (- y))| . 1))
     (1 1
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor (- x) y)| . 2))
     (1 1 (:REWRITE |(floor (- x) y)| . 1))
     (1 1
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(MV-NTH-0-OF-UBYTE8=>HEXCHARS-OF-UNSIGNED-BYTE-FIX)
(MV-NTH-1-OF-UBYTE8=>HEXCHARS-OF-UNSIGNED-BYTE-FIX)
(HEXCHARS=>UBYTE8)
(RETURN-TYPE-OF-HEXCHARS=>UBYTE8)
(HEXCHARS=>UBYTE8-OF-UBYTE8=>HEXCHARS
     (256 256
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (256 256
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (256 256
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (256 256
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (148 53 (:REWRITE DEFAULT-TIMES-2))
     (136 2 (:REWRITE FLOOR-ZERO . 3))
     (118 26 (:REWRITE INTEGERP-MINUS-X))
     (106 2 (:REWRITE CANCEL-MOD-+))
     (106 2 (:REWRITE CANCEL-FLOOR-+))
     (104 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (96 1 (:REWRITE DEFAULT-PLUS-1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (70 2 (:REWRITE MOD-X-Y-=-X . 4))
     (70 2 (:REWRITE FLOOR-ZERO . 5))
     (68 8 (:REWRITE |(* (- x) y)|))
     (62 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (62 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (60 2 (:REWRITE MOD-X-Y-=-X . 3))
     (60 2 (:REWRITE FLOOR-ZERO . 4))
     (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (53 53 (:REWRITE DEFAULT-TIMES-1))
     (44 2 (:REWRITE MOD-ZERO . 3))
     (44 2 (:REWRITE FLOOR-=-X/Y . 3))
     (44 2 (:REWRITE FLOOR-=-X/Y . 2))
     (40 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (40 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (40 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (40 8 (:REWRITE DEFAULT-MINUS))
     (36 8 (:REWRITE |(- (* c x))|))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (36 2 (:REWRITE MOD-ZERO . 4))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (35 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (32 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (32 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (29 1 (:REWRITE DEFAULT-PLUS-2))
     (27 27 (:REWRITE THE-FLOOR-BELOW))
     (27 27 (:REWRITE THE-FLOOR-ABOVE))
     (27 27 (:REWRITE DEFAULT-LESS-THAN-2))
     (27 25
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (27 25
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (25 25
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (25 25
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (25 25 (:REWRITE INTEGERP-<-CONSTANT))
     (25 25 (:REWRITE CONSTANT-<-INTEGERP))
     (25 25
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (25 25
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (25 25
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (25 25
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (25 25 (:REWRITE |(< c (- x))|))
     (25 25
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (25 25
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (25 25
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (25 25
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (25 25 (:REWRITE |(< (/ x) (/ y))|))
     (25 25 (:REWRITE |(< (- x) c)|))
     (25 25 (:REWRITE |(< (- x) (- y))|))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (22 22 (:REWRITE REDUCE-INTEGERP-+))
     (22 22 (:META META-INTEGERP-CORRECT))
     (22 2 (:REWRITE DEFAULT-MOD-RATIO))
     (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (22 1 (:LINEAR MOD-BOUNDS-3))
     (22 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (16 4 (:REWRITE RATIONALP-X))
     (10 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (10 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (10 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (10 2 (:REWRITE MOD-X-Y-=-X . 2))
     (10 2 (:REWRITE MOD-CANCEL-*-CONST))
     (10 2 (:REWRITE FLOOR-ZERO . 2))
     (10 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (10 2 (:REWRITE FLOOR-CANCEL-*-CONST))
     (10 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (10 2
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (6 2
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (6 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 2
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (6 2
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 2
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (6 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (6 2
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (6 2
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (3 3
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-FIX))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE DEFAULT-MOD-1))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
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
     (2 2 (:REWRITE |(floor x (- y))| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 1))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(floor (- x) y)| . 2))
     (2 2 (:REWRITE |(floor (- x) y)| . 1))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (2 2
        (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(UBYTE8=>HEXCHARS-OF-HEXCHARS=>UBYTE8
 (492 12 (:REWRITE |(* x (+ y z))|))
 (394 171 (:REWRITE DEFAULT-TIMES-2))
 (350 38
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (346 2 (:REWRITE |(floor (+ x r) i)|))
 (260 2 (:REWRITE FLOOR-ZERO . 3))
 (231 171 (:REWRITE DEFAULT-TIMES-1))
 (202 4 (:REWRITE MOD-ZERO . 3))
 (202 4 (:REWRITE FLOOR-=-X/Y . 3))
 (202 4 (:REWRITE FLOOR-=-X/Y . 2))
 (196 14 (:REWRITE |(* y (* x z))|))
 (190 4 (:REWRITE MOD-X-Y-=-X . 4))
 (184 4 (:REWRITE FLOOR-ZERO . 5))
 (174 36 (:REWRITE INTEGERP-<-CONSTANT))
 (174 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (174 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (162 58 (:REWRITE DEFAULT-PLUS-2))
 (162 58 (:REWRITE DEFAULT-PLUS-1))
 (144 4 (:REWRITE DEFAULT-MOD-RATIO))
 (144 4 (:REWRITE DEFAULT-FLOOR-RATIO))
 (120 4 (:REWRITE MOD-ZERO . 4))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (116 116
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (94 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (88 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (88 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (82 34
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (75 75
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (68 18 (:REWRITE DEFAULT-MINUS))
 (54 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (40 36
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 36
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (38 34
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (38 8
     (:REWRITE STR::UPCASE-CHAR-DOES-NOTHING-UNLESS-DOWN-ALPHA-P))
 (36 36
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (36 36 (:REWRITE CONSTANT-<-INTEGERP))
 (36 36
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (36 36
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (36 36
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (36 36
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (36 36 (:REWRITE |(< c (- x))|))
 (36 36
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (36 36
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (36 36
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (36 36 (:REWRITE |(< (/ x) (/ y))|))
 (36 36 (:REWRITE |(< (- x) c)|))
 (36 36 (:REWRITE |(< (- x) (- y))|))
 (34 34 (:REWRITE SIMPLIFY-SUMS-<))
 (32 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (32 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (30 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (28 14 (:REWRITE |(* a (/ a) b)|))
 (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (26 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (26 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (26 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (26 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (22 6 (:REWRITE ACL2-NUMBERP-X))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:META META-INTEGERP-CORRECT))
 (18 6
     (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-NONZERO-HEX-DIGIT-CHAR-P))
 (18 6
     (:REWRITE STR::DOWN-ALPHA-P-WHEN-UP-ALPHA-P))
 (18 2 (:REWRITE MOD-X-Y-=-X . 2))
 (18 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (18 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (17 17
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (16 16 (:REWRITE |(< (+ (- c) x) y)|))
 (14 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 2 (:REWRITE FLOOR-ZERO . 2))
 (12 12
     (:TYPE-PRESCRIPTION STR::UP-ALPHA-P$INLINE))
 (12 12
     (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGIT-CHAR-P$INLINE))
 (12 12
     (:TYPE-PRESCRIPTION STR::DOWN-ALPHA-P$INLINE))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12
  12
  (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-CHAR-LISTP))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (10 4 (:REWRITE DEFAULT-MOD-1))
 (10 4 (:REWRITE DEFAULT-FLOOR-1))
 (8 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4
    (:REWRITE STR::HEX-DIGIT-VAL-UPPER-BOUND))
 (4 4 (:REWRITE DEFAULT-MOD-2))
 (4 4 (:REWRITE DEFAULT-FLOOR-2))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-RATIONALP-CORRECT)))
(UBYTE8S=>HEXCHARS-AUX
     (49 3 (:REWRITE SUBSETP-OF-CONS))
     (24 3 (:DEFINITION MEMBER-EQUAL))
     (17 17 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (8 8
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (6 6 (:REWRITE SUBSETP-TRANS2))
     (6 6 (:REWRITE SUBSETP-TRANS))
     (6 6 (:REWRITE SUBSETP-MEMBER . 2))
     (6 6 (:REWRITE SUBSETP-MEMBER . 1))
     (6 6
        (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR)))
(UBYTE8S=>HEXCHARS)
(HEX-DIGIT-CHAR-LISTP-OF-UBYTE8S=>HEXCHARS
     (61 3 (:REWRITE SUBSETP-OF-CONS))
     (36 3 (:DEFINITION MEMBER-EQUAL))
     (32 9
         (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
     (17 17 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (8 8 (:REWRITE SUBSETP-TRANS2))
     (8 8 (:REWRITE SUBSETP-TRANS))
     (8 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (8 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (6 6 (:REWRITE SUBSETP-MEMBER . 2))
     (6 6 (:REWRITE SUBSETP-MEMBER . 1))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR)))
(VERIFY-GUARDS-LEMMA (67 34 (:REWRITE DEFAULT-CAR))
                     (59 26 (:REWRITE DEFAULT-CDR))
                     (13 13 (:REWRITE REV-WHEN-NOT-CONSP))
                     (10 10
                         (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
                     (4 4
                        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV)))
(UBYTE8S=>HEXCHARS (10 10 (:REWRITE DEFAULT-CAR))
                   (8 8 (:REWRITE DEFAULT-CDR))
                   (4 4
                      (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR)))
(UBYTE8S=>HEXCHARS-OF-UNSIGNED-BYTE-LIST-FIX
     (52 4
         (:REWRITE UNSIGNED-BYTE-FIX-WHEN-UNSIGNED-BYTE-P))
     (45 9
         (:REWRITE UNSIGNED-BYTE-LIST-FIX-WHEN-UNSIGNED-BYTE-LISTP))
     (25 25
         (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
     (24 4 (:DEFINITION UNSIGNED-BYTE-P))
     (20 4
         (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
     (20 4 (:DEFINITION INTEGER-RANGE-P))
     (14 13
         (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
     (13 13
         (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (7 7 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE DEFAULT-CAR))
     (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (4 4
        (:REWRITE UNSIGNED-BYTE-FIX-OF-NFIX-BITS-NORMALIZE-CONST)))
(EVENP-OF-LEN-OF-UBYTE8S=>HEXCHARS (19 10 (:REWRITE DEFAULT-+-2))
                                   (13 7 (:REWRITE DEFAULT-*-2))
                                   (12 10 (:REWRITE DEFAULT-CDR))
                                   (10 10 (:REWRITE DEFAULT-+-1))
                                   (8 7 (:REWRITE DEFAULT-*-1))
                                   (5 5 (:REWRITE DEFAULT-CAR)))
(UBYTE8S=>HEXCHARS-OF-APPEND (50 19 (:REWRITE DEFAULT-CDR))
                             (30 27 (:REWRITE DEFAULT-CAR))
                             (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
                             (12 4 (:REWRITE CAR-OF-APPEND))
                             (8 8 (:REWRITE CONSP-OF-APPEND))
                             (4 4 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(HEXCHARS=>UBYTE8S-AUX
     (214 102 (:REWRITE DEFAULT-+-2))
     (137 102 (:REWRITE DEFAULT-+-1))
     (126 9 (:DEFINITION LENGTH))
     (81 7 (:DEFINITION MEMBER-EQUAL))
     (75 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
     (72 18 (:REWRITE COMMUTATIVITY-OF-+))
     (72 18 (:DEFINITION INTEGER-ABS))
     (48 8
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (31 23 (:REWRITE DEFAULT-<-2))
     (28 28 (:REWRITE DEFAULT-CAR))
     (27 27
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (27 23 (:REWRITE DEFAULT-<-1))
     (27 18 (:REWRITE STR::CONSP-OF-EXPLODE))
     (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
     (18 9
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (16 9 (:REWRITE DEFAULT-*-2))
     (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (14 14 (:REWRITE SUBSETP-MEMBER . 2))
     (14 14 (:REWRITE SUBSETP-MEMBER . 1))
     (12 12 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
     (11 9 (:REWRITE DEFAULT-*-1))
     (9 9
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (9 9 (:REWRITE DEFAULT-REALPART))
     (9 9 (:REWRITE DEFAULT-NUMERATOR))
     (9 9 (:REWRITE DEFAULT-IMAGPART))
     (9 9 (:REWRITE DEFAULT-DENOMINATOR))
     (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (8 8
        (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
     (8 8 (:REWRITE SET::IN-SET))
     (6 6
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (5 5
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
     (3 3 (:REWRITE SUBSETP-TRANS2))
     (3 3 (:REWRITE SUBSETP-TRANS))
     (3 3 (:REWRITE MEMBER-SELF))
     (2 2
        (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
     (1 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (1 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (1 1 (:REWRITE MEMBER-OF-CAR)))
(HEXCHARS=>UBYTE8S (190 89 (:REWRITE DEFAULT-+-2))
                   (126 9 (:DEFINITION LENGTH))
                   (124 89 (:REWRITE DEFAULT-+-1))
                   (99 9 (:DEFINITION LEN))
                   (75 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
                   (72 18 (:REWRITE COMMUTATIVITY-OF-+))
                   (72 18 (:DEFINITION INTEGER-ABS))
                   (63 6 (:DEFINITION MEMBER-EQUAL))
                   (31 23 (:REWRITE DEFAULT-<-2))
                   (27 27
                       (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                   (27 23 (:REWRITE DEFAULT-<-1))
                   (27 18 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (23 23 (:REWRITE DEFAULT-CAR))
                   (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
                   (18 9
                       (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                   (12 12 (:REWRITE SUBSETP-MEMBER . 2))
                   (12 12 (:REWRITE SUBSETP-MEMBER . 1))
                   (12 12 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
                   (9 9 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (9 9 (:TYPE-PRESCRIPTION LEN))
                   (9 9
                      (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (9 9 (:REWRITE DEFAULT-REALPART))
                   (9 9 (:REWRITE DEFAULT-NUMERATOR))
                   (9 9 (:REWRITE DEFAULT-IMAGPART))
                   (9 9 (:REWRITE DEFAULT-DENOMINATOR))
                   (3 3 (:REWRITE MEMBER-SELF)))
(RETURN-TYPE-OF-HEXCHARS=>UBYTE8S
     (32 8
         (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
     (9 9
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (3 3 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
(VERIFY-GUARDS-LEMMA (114 19
                          (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
                     (82 67 (:REWRITE DEFAULT-CDR))
                     (38 38 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
                     (38 23 (:REWRITE DEFAULT-CAR))
                     (38 19 (:REWRITE SET::NONEMPTY-MEANS-SET))
                     (31 16 (:REWRITE DEFAULT-+-2))
                     (19 19 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
                     (19 19
                         (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
                     (19 19 (:REWRITE SET::IN-SET))
                     (17 9 (:REWRITE DEFAULT-*-2))
                     (16 16 (:REWRITE DEFAULT-+-1))
                     (10 10 (:REWRITE REV-WHEN-NOT-CONSP))
                     (10 9 (:REWRITE DEFAULT-*-1))
                     (5 5
                        (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP)))
(HEXCHARS=>UBYTE8S (54 9
                       (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
                   (41 41 (:REWRITE DEFAULT-CDR))
                   (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
                   (18 9 (:REWRITE SET::NONEMPTY-MEANS-SET))
                   (18 9 (:REWRITE DEFAULT-+-2))
                   (16 16 (:REWRITE DEFAULT-CAR))
                   (13 8 (:REWRITE DEFAULT-*-2))
                   (11 8 (:REWRITE DEFAULT-*-1))
                   (9 9 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
                   (9 9
                      (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
                   (9 9 (:REWRITE SET::IN-SET))
                   (9 9 (:REWRITE DEFAULT-+-1))
                   (2 2
                      (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
                   (1 1 (:REWRITE SUBSETP-TRANS2))
                   (1 1 (:REWRITE SUBSETP-TRANS)))
(HEXCHARS=>UBYTE8S-OF-APPEND (157 86 (:REWRITE DEFAULT-CDR))
                             (93 49 (:REWRITE DEFAULT-CAR))
                             (39 39 (:TYPE-PRESCRIPTION TRUE-LISTP))
                             (34 18 (:REWRITE DEFAULT-+-2))
                             (19 11 (:REWRITE DEFAULT-*-2))
                             (18 18 (:REWRITE DEFAULT-+-1))
                             (14 11 (:REWRITE DEFAULT-*-1))
                             (9 3 (:REWRITE CAR-OF-APPEND))
                             (6 6 (:REWRITE CONSP-OF-APPEND))
                             (6 6 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(HEXCHARS=>UBYTE8S-OF-UBYTE8S=>HEXCHARS
     (52 4
         (:REWRITE UNSIGNED-BYTE-FIX-WHEN-UNSIGNED-BYTE-P))
     (30 6
         (:REWRITE UNSIGNED-BYTE-LIST-FIX-WHEN-UNSIGNED-BYTE-LISTP))
     (24 8
         (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
     (19 19
         (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
     (19 16 (:REWRITE DEFAULT-CDR))
     (16 16 (:REWRITE DEFAULT-<-2))
     (16 16 (:REWRITE DEFAULT-<-1))
     (16 14 (:REWRITE DEFAULT-CAR))
     (11 10
         (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
     (10 10
         (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (4 4
        (:REWRITE UNSIGNED-BYTE-FIX-OF-NFIX-BITS-NORMALIZE-CONST)))
(UBYTE8S=>HEXCHARS-OF-HEXCHARS=>UBYTE8S
 (102 17
      (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (79 78 (:REWRITE DEFAULT-CDR))
 (36 6
     (:REWRITE STR::UPCASE-CHAR-DOES-NOTHING-UNLESS-DOWN-ALPHA-P))
 (34 34 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (34 17 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (33 17 (:REWRITE DEFAULT-+-2))
 (24
  8
  (:REWRITE
    STR::UPCASE-CHARLIST-DOES-NOTHING-UNLESS-CHARLIST-HAS-SOME-DOWN-ALPHA-P))
 (18 6
     (:REWRITE STR::DOWN-ALPHA-P-WHEN-UP-ALPHA-P))
 (17 17 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (17 17
     (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (17 17 (:REWRITE SET::IN-SET))
 (17 17 (:REWRITE DEFAULT-+-1))
 (17 10 (:REWRITE DEFAULT-*-2))
 (16 16
     (:TYPE-PRESCRIPTION STR::CHARLIST-HAS-SOME-DOWN-ALPHA-P))
 (15 14 (:REWRITE DEFAULT-CAR))
 (13 10 (:REWRITE DEFAULT-*-1))
 (12 12
     (:TYPE-PRESCRIPTION STR::UP-ALPHA-P$INLINE))
 (12 12
     (:TYPE-PRESCRIPTION STR::DOWN-ALPHA-P$INLINE))
 (8 8
    (:REWRITE STR::UPCASE-CHARLIST-WHEN-ATOM))
 (4 4
    (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS)))
