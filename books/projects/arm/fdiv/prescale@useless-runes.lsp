(RTL::MUL)
(D (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
   (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
   (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(X (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
   (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
   (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SIGB-BOUNDS
 (8 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (4 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::MOD-SIGB
 (301 7 (:REWRITE MOD-X-Y-=-X . 4))
 (289 7 (:REWRITE MOD-X-Y-=-X . 3))
 (287 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (283 283
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (283 283
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (283 283
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (270 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (224 7 (:REWRITE RTL::MOD-DOES-NOTHING))
 (213 41 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (213 41 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (213 41
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (213 41
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (189 7 (:REWRITE MOD-ZERO . 3))
 (181 7 (:REWRITE MOD-ZERO . 4))
 (98 7 (:REWRITE DEFAULT-MOD-RATIO))
 (80 16 (:REWRITE |(* y x)|))
 (76 38
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (76 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (69 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (54 2 (:LINEAR MOD-BOUNDS-3))
 (50 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (49 7 (:REWRITE MOD-X-Y-=-X . 2))
 (48 32 (:REWRITE DEFAULT-TIMES-2))
 (48 32 (:REWRITE DEFAULT-TIMES-1))
 (45 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (42 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (42 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (42 7
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (42 7
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (41 41 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (41 41
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (41 41 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (41 41
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 38 (:REWRITE SIMPLIFY-SUMS-<))
 (38 38
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (38 38
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (38 38
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (24 4 (:LINEAR MOD-BOUNDS-2))
 (21
   21
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (21
  21
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 17
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (17 17
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (14 7 (:REWRITE DEFAULT-MOD-1))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (7 7
    (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE DEFAULT-MOD-2))
 (7 7 (:REWRITE |(mod x (- y))| . 3))
 (7 7 (:REWRITE |(mod x (- y))| . 2))
 (7 7 (:REWRITE |(mod x (- y))| . 1))
 (7 7
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (7 7
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (7 7
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::BITS-SIGB
 (411 13 (:REWRITE RTL::INTEGERP-FL))
 (268 50 (:REWRITE DEFAULT-TIMES-2))
 (232 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (213 5 (:REWRITE MOD-X-Y-=-X . 4))
 (191 5 (:REWRITE MOD-X-Y-=-X . 3))
 (137 51 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (128 5 (:REWRITE MOD-ZERO . 4))
 (118 57 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (118 57
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (118 57
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (118 50 (:REWRITE DEFAULT-TIMES-1))
 (114 5 (:REWRITE MOD-ZERO . 3))
 (112 8 (:REWRITE DEFAULT-MOD-RATIO))
 (96 3 (:REWRITE RTL::MOD-DOES-NOTHING))
 (91 56 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (86 51 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (86 51
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (83 57 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (57 57 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (57 57
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (57 57 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (57 57
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (51 51 (:TYPE-PRESCRIPTION NATP))
 (43 1 (:LINEAR RTL::MOD-BND-2))
 (42 6 (:REWRITE |(mod x 1)|))
 (41 1 (:LINEAR RTL::MOD-BND-1))
 (40 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (38 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (36 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (35 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (34 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (31 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (30 18
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (30 18
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 17 (:REWRITE DEFAULT-PLUS-2))
 (28 28 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:REWRITE INTEGERP-MINUS-X))
 (28 28 (:META META-INTEGERP-CORRECT))
 (24 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (23 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (23 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (23 5 (:REWRITE MOD-X-Y-=-X . 2))
 (21 17 (:REWRITE DEFAULT-PLUS-1))
 (21 3 (:REWRITE RTL::MOD-BY-1))
 (20 10 (:REWRITE |(* 1 x)|))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18 (:REWRITE CONSTANT-<-INTEGERP))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (18 18 (:REWRITE |(< (- x) (- y))|))
 (18 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (18 5
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (18 5
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (16 8 (:REWRITE DEFAULT-MOD-1))
 (16 1 (:LINEAR MOD-BOUNDS-3))
 (15 15
     (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (15 15 (:TYPE-PRESCRIPTION ABS))
 (14 14
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 13 (:REWRITE NORMALIZE-ADDENDS))
 (13 7
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12 12 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:REWRITE DEFAULT-MOD-2))
 (8 4 (:REWRITE |(* a (/ a) b)|))
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
 (6 6 (:LINEAR RTL::N<=FL-LINEAR))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5 5
    (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5 (:REWRITE |(mod x (- y))| . 3))
 (5 5 (:REWRITE |(mod x (- y))| . 2))
 (5 5 (:REWRITE |(mod x (- y))| . 1))
 (5 5
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (5 5
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (5 5
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (4 4
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 2 (:LINEAR MOD-BOUNDS-2))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:LINEAR RTL::MOD-BND-3)))
(RTL::BITS-SIGB-BOUNDS
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (38 19 (:REWRITE DEFAULT-PLUS-2))
     (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (23 19 (:REWRITE DEFAULT-PLUS-1))
     (16 9 (:REWRITE DEFAULT-TIMES-2))
     (14 2 (:REWRITE SIMPLIFY-SUMS-<))
     (14 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (14 2 (:REWRITE RTL::INTEGERP-FL))
     (12 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (11 9 (:REWRITE DEFAULT-TIMES-1))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (4 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::D-BOUNDS (223 127 (:REWRITE DEFAULT-TIMES-2))
               (194 194
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (194 194
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (194 194
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (129 127 (:REWRITE DEFAULT-TIMES-1))
               (129 13 (:REWRITE CONSTANT-<-INTEGERP))
               (110 110
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (110 110
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (84 27 (:REWRITE DEFAULT-LESS-THAN-1))
               (74 74 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
               (74 74 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
               (74 74 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
               (73 27
                   (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
               (73 27
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
               (65 27 (:REWRITE DEFAULT-LESS-THAN-2))
               (64 64
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (52 13
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (52 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (46 46
                   (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
               (46 46 (:TYPE-PRESCRIPTION ABS))
               (36 8
                   (:REWRITE |(<= (/ x) y) with (< x 0)|))
               (36 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
               (27 27 (:REWRITE THE-FLOOR-BELOW))
               (27 27 (:REWRITE THE-FLOOR-ABOVE))
               (24 13 (:REWRITE SIMPLIFY-SUMS-<))
               (18 6 (:REWRITE DEFAULT-PLUS-2))
               (17 13 (:REWRITE INTEGERP-<-CONSTANT))
               (16 8
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (16 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
               (13 13
                   (:REWRITE REMOVE-STRICT-INEQUALITIES))
               (13 13
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
               (13 13
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
               (13 13
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
               (13 13
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
               (13 13 (:REWRITE |(< c (- x))|))
               (13 13
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
               (13 13
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
               (13 13
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
               (13 13
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
               (13 13 (:REWRITE |(< (/ x) (/ y))|))
               (13 13 (:REWRITE |(< (- x) c)|))
               (13 13 (:REWRITE |(< (- x) (- y))|))
               (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
               (9 9 (:REWRITE SUBSETP-MEMBER . 4))
               (9 9 (:REWRITE SUBSETP-MEMBER . 3))
               (9 9 (:REWRITE SUBSETP-MEMBER . 2))
               (9 9 (:REWRITE SUBSETP-MEMBER . 1))
               (9 9 (:REWRITE REDUCE-INTEGERP-+))
               (9 9 (:REWRITE INTERSECTP-MEMBER . 3))
               (9 9 (:REWRITE INTERSECTP-MEMBER . 2))
               (9 9 (:REWRITE INTEGERP-MINUS-X))
               (9 9 (:META META-INTEGERP-CORRECT))
               (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (8 8
                  (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (8 8
                  (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (8 8
                  (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (8 8 (:REWRITE |(equal c (/ x))|))
               (8 8 (:REWRITE |(equal c (- x))|))
               (8 8 (:REWRITE |(equal (/ x) c)|))
               (8 8 (:REWRITE |(equal (/ x) (/ y))|))
               (8 8 (:REWRITE |(equal (- x) c)|))
               (8 8 (:REWRITE |(equal (- x) (- y))|))
               (8 6 (:REWRITE DEFAULT-PLUS-1))
               (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
               (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
               (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
               (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
               (7 7
                  (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
               (7 7
                  (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
               (7 7
                  (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
               (4 4
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (4 4 (:REWRITE NORMALIZE-ADDENDS))
               (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
               (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
               (2 2 (:REWRITE |(< y (+ (- c) x))|))
               (2 2 (:REWRITE |(< x (+ c/d y))|))
               (1 1
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (1 1
                  (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::X-BOUNDS (466 466
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
               (466 466
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (466 466
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (466 466
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (367 211 (:REWRITE DEFAULT-TIMES-2))
               (211 211 (:REWRITE DEFAULT-TIMES-1))
               (182 68 (:REWRITE DEFAULT-LESS-THAN-1))
               (166 52
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (166 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (164 52 (:REWRITE SIMPLIFY-SUMS-<))
               (152 68 (:REWRITE DEFAULT-LESS-THAN-2))
               (140 140
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
               (140 140
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
               (140 140
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (140 140
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
               (140 140
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (140 140
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
               (112 112
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (110 52
                    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
               (110 52
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
               (68 68 (:REWRITE THE-FLOOR-BELOW))
               (68 68 (:REWRITE THE-FLOOR-ABOVE))
               (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-3L))
               (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-2L))
               (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-1L))
               (60 52
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
               (58 58
                   (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
               (58 58 (:TYPE-PRESCRIPTION ABS))
               (52 52 (:REWRITE REMOVE-WEAK-INEQUALITIES))
               (52 52
                   (:REWRITE REMOVE-STRICT-INEQUALITIES))
               (52 52 (:REWRITE INTEGERP-<-CONSTANT))
               (52 52 (:REWRITE CONSTANT-<-INTEGERP))
               (52 52
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
               (52 52
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
               (52 52
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
               (52 52
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
               (52 52 (:REWRITE |(< c (- x))|))
               (52 52
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
               (52 52
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
               (52 52
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
               (52 52 (:REWRITE |(< (/ x) (/ y))|))
               (52 52 (:REWRITE |(< (- x) c)|))
               (52 52 (:REWRITE |(< (- x) (- y))|))
               (34 34 (:REWRITE RTL::BITS-REVERSE-INDICES))
               (34 34 (:REWRITE RTL::BITS-NEG-INDICES))
               (20 10
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (20 10 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
               (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (10 10
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (10 10
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (10 10
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (10 10 (:REWRITE |(equal c (/ x))|))
               (10 10 (:REWRITE |(equal c (- x))|))
               (10 10 (:REWRITE |(equal (/ x) c)|))
               (10 10 (:REWRITE |(equal (/ x) (/ y))|))
               (10 10 (:REWRITE |(equal (- x) c)|))
               (10 10 (:REWRITE |(equal (- x) (- y))|))
               (9 9 (:REWRITE SUBSETP-MEMBER . 4))
               (9 9 (:REWRITE SUBSETP-MEMBER . 3))
               (9 9 (:REWRITE SUBSETP-MEMBER . 2))
               (9 9 (:REWRITE SUBSETP-MEMBER . 1))
               (9 9 (:REWRITE INTERSECTP-MEMBER . 3))
               (9 9 (:REWRITE INTERSECTP-MEMBER . 2))
               (3 3
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (2 2 (:REWRITE REDUCE-INTEGERP-+))
               (2 2 (:REWRITE INTEGERP-MINUS-X))
               (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::DIV1)
(RTL::DIV2)
(RTL::DIV3)
(RTL::DIVSUM)
(RTL::DIVCAR (8 8
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (3 3
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (3 3
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (3 3
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::DIV*)
(RTL::REM1)
(RTL::REM2)
(RTL::REM3)
(RTL::REMSUM)
(RTL::REMCAR (8 8
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (3 3
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (3 3
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (3 3
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::SIGABAR)
(RTL::SIGCMP)
(RTL::SIGALTSIGB)
(RTL::REMCARBITS)
(RTL::REMSUMBITS)
(RTL::REMCIN)
(RTL::REMBITS)
(Q1 (2 2
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1)))
(RTL::RP-1*)
(RTL::EXPQ* (4 4 (:TYPE-PRESCRIPTION RTL::SI))
            (4 4 (:TYPE-PRESCRIPTION RTL::INT-SI)))
(RTL::RN-1*)
(RTL::PRESCALE-LEMMA)
(RTL::Q1-VALS
 (80 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (80 9 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (60 5 (:REWRITE RTL::NEG-BITN-0))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (28 2 (:REWRITE DEFAULT-MOD-RATIO))
 (20 20 (:TYPE-PRESCRIPTION RTL::REMBITS))
 (15 5 (:REWRITE RTL::NEG-BITN-1))
 (15 5 (:REWRITE RTL::BVECP-BITN-0))
 (14 8 (:REWRITE DEFAULT-LOGAND-2))
 (13 8 (:REWRITE DEFAULT-LOGAND-1))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 6 (:REWRITE DEFAULT-TIMES-2))
 (10 2 (:REWRITE |(* y x)|))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (8 6 (:REWRITE DEFAULT-TIMES-1))
 (7
   7
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (7
  7
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5 (:REWRITE RTL::BITN-NEG))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 2 (:REWRITE DEFAULT-MOD-1))
 (3 3 (:REWRITE SUBSETP-MEMBER . 4))
 (3 3 (:REWRITE SUBSETP-MEMBER . 3))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 3))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 2))
 (3 1 (:REWRITE RTL::BITN-BVECP-1))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE |(mod x 2)| . 2))
 (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::QUOT
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(R
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::MOD-3-VAL2
     (339 339
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (339 339
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (339 339
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (339 339
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (330 66 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (330 66 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (273 9 (:REWRITE MOD-X-Y-=-X . 4))
     (241 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (205 9 (:REWRITE MOD-X-Y-=-X . 3))
     (190 66
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (190 66
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (177 9 (:REWRITE MOD-ZERO . 3))
     (177 9 (:REWRITE RTL::MOD-DOES-NOTHING))
     (145 9 (:REWRITE MOD-ZERO . 4))
     (128 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (123 23
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (99 9 (:REWRITE DEFAULT-MOD-RATIO))
     (76 19 (:REWRITE |(* y x)|))
     (73 17
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (73 17 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (71 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (70 35 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (66 66 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (66 66 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (66 66
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (66 66 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (66 66
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (66 66 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (60 32 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (60 32 (:REWRITE DEFAULT-LESS-THAN-1))
     (45 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (45 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (45 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (45 9 (:REWRITE MOD-X-Y-=-X . 2))
     (45 9
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (45 9
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (38 38 (:REWRITE DEFAULT-TIMES-2))
     (38 38 (:REWRITE DEFAULT-TIMES-1))
     (35 35
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (35 35 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (35 35 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (35 35 (:TYPE-PRESCRIPTION NATP))
     (35 35
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (32 32 (:REWRITE THE-FLOOR-BELOW))
     (32 32 (:REWRITE THE-FLOOR-ABOVE))
     (32 32 (:REWRITE SIMPLIFY-SUMS-<))
     (32 32
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (32 32
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (32 32
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (32 32 (:REWRITE INTEGERP-<-CONSTANT))
     (32 32 (:REWRITE DEFAULT-LESS-THAN-2))
     (32 32 (:REWRITE CONSTANT-<-INTEGERP))
     (32 32
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (32 32
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (32 32
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (32 32
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (32 32 (:REWRITE |(< c (- x))|))
     (32 32
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (32 32
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (32 32
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (32 32
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (32 32 (:REWRITE |(< (/ x) (/ y))|))
     (32 32 (:REWRITE |(< (- x) c)|))
     (32 32 (:REWRITE |(< (- x) (- y))|))
     (30 6 (:REWRITE |(+ y x)|))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (26 26 (:REWRITE DEFAULT-PLUS-2))
     (26 26 (:REWRITE DEFAULT-PLUS-1))
     (26 1 (:REWRITE MOD-ZERO . 1))
     (25 6 (:REWRITE |(+ c (+ d x))|))
     (23 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (22 1 (:LINEAR MOD-BOUNDS-3))
     (19 19
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (17 17
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (17 17 (:REWRITE |(equal c (/ x))|))
     (17 17 (:REWRITE |(equal c (- x))|))
     (17 17 (:REWRITE |(equal (/ x) c)|))
     (17 17 (:REWRITE |(equal (/ x) (/ y))|))
     (17 17 (:REWRITE |(equal (- x) c)|))
     (17 17 (:REWRITE |(equal (- x) (- y))|))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11 (:META META-INTEGERP-CORRECT))
     (11 1 (:REWRITE |(+ y (+ x z))|))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (9 9
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (9 9
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (9 9 (:REWRITE DEFAULT-MOD-2))
     (9 9 (:REWRITE DEFAULT-MOD-1))
     (9 9 (:REWRITE |(mod x (- y))| . 3))
     (9 9 (:REWRITE |(mod x (- y))| . 2))
     (9 9 (:REWRITE |(mod x (- y))| . 1))
     (9 9
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (9 9
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (9 9
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE SUBSETP-MEMBER . 4))
     (6 6 (:REWRITE INTERSECTP-MEMBER . 3))
     (6 6 (:REWRITE INTERSECTP-MEMBER . 2))
     (5 5 (:REWRITE SUBSETP-MEMBER . 2))
     (5 5 (:REWRITE SUBSETP-MEMBER . 1))
     (5 5 (:REWRITE |(+ 0 x)|))
     (5 1 (:REWRITE MOD-ZERO . 2))
     (4 4
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:LINEAR RTL::MOD-BND-3)))
(RTL::Q-VALS
 (14688 288 (:REWRITE RTL::BITS-TAIL-GEN))
 (10969 10969
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10969 10969
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10969 10969
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10969 10969
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (9675 1935 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (9675 1935 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (8610 287 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (8328 287 (:REWRITE MOD-X-Y-=-X . 3))
 (7175 287 (:REWRITE RTL::MOD-DOES-NOTHING))
 (6675 1935
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (6675 1935
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6655 1935 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (6314 287 (:REWRITE MOD-ZERO . 3))
 (4246 4246
       (:TYPE-PRESCRIPTION RTL::BITS-NONNEGATIVE-INTEGERP-TYPE))
 (4054 718
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3614 334 (:REWRITE RTL::NEG-BITN-0))
 (3418 3418 (:TYPE-PRESCRIPTION LOGNOT))
 (3408 718
       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3372 2150 (:REWRITE DEFAULT-PLUS-2))
 (2800 2150 (:REWRITE DEFAULT-PLUS-1))
 (1950 802
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1935 1935 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1935 1935
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1935 1935
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1935 1935
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1935 1935
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1792 56 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1728 1152
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1728 1152
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1728 1152 (:REWRITE DEFAULT-LESS-THAN-1))
 (1574 334 (:REWRITE RTL::BVECP-BITN-0))
 (1568 1568
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1568 1568 (:REWRITE NORMALIZE-ADDENDS))
 (1508 754 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (1464 287 (:REWRITE MOD-X-Y-=-X . 4))
 (1463 287 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1448 287 (:REWRITE MOD-ZERO . 4))
 (1435 287 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1435 287 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1435 287 (:REWRITE MOD-X-Y-=-X . 2))
 (1435 287
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1435 287
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1274 1266 (:REWRITE DEFAULT-TIMES-2))
 (1266 1266 (:REWRITE DEFAULT-TIMES-1))
 (1232 56 (:LINEAR MOD-BOUNDS-3))
 (1152 1152 (:REWRITE THE-FLOOR-BELOW))
 (1152 1152 (:REWRITE THE-FLOOR-ABOVE))
 (1152 1152 (:REWRITE SIMPLIFY-SUMS-<))
 (1152 1152
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1152 1152
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1152 1152
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1152 1152 (:REWRITE INTEGERP-<-CONSTANT))
 (1152 1152 (:REWRITE DEFAULT-LESS-THAN-2))
 (1152 1152 (:REWRITE CONSTANT-<-INTEGERP))
 (1152 1152
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1152 1152
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1152 1152
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1152 1152
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1152 1152 (:REWRITE |(< c (- x))|))
 (1152 1152
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1152 1152
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1152 1152
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1152 1152
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1152 1152 (:REWRITE |(< (/ x) (/ y))|))
 (1152 1152 (:REWRITE |(< (- x) c)|))
 (1152 1152 (:REWRITE |(< (- x) (- y))|))
 (985 985
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (985 985
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (985 985
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (985 985
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (976 976
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (976 976 (:REWRITE RTL::BITS-NEG-INDICES))
 (950 334 (:REWRITE RTL::NEG-BITN-1))
 (864 288 (:REWRITE RTL::BITS-TAIL))
 (860 100 (:REWRITE ACL2-NUMBERP-X))
 (802 802
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (754 754
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (754 754 (:TYPE-PRESCRIPTION NATP))
 (754 754
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (750 750
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (750 750 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (728 56 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (718 718 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (718 718
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (718 718 (:REWRITE |(equal c (/ x))|))
 (718 718 (:REWRITE |(equal c (- x))|))
 (718 718 (:REWRITE |(equal (/ x) c)|))
 (718 718 (:REWRITE |(equal (/ x) (/ y))|))
 (718 718 (:REWRITE |(equal (- x) c)|))
 (718 718 (:REWRITE |(equal (- x) (- y))|))
 (652 372 (:REWRITE |(+ c (+ d x))|))
 (632 632
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (584 584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (584
   584
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (584
  584
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (584 584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (584 584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (584
     584
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (584 584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (584 584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (584 584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (576 288 (:REWRITE DEFAULT-LOGNOT))
 (560 112 (:LINEAR MOD-BOUNDS-2))
 (464 464 (:REWRITE REDUCE-INTEGERP-+))
 (464 464 (:REWRITE INTEGERP-MINUS-X))
 (464 464 (:META META-INTEGERP-CORRECT))
 (450 450
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (440 104 (:REWRITE RATIONALP-X))
 (334 334 (:REWRITE RTL::BITN-NEG))
 (316 316 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (316 316 (:REWRITE RTL::BITS-BVECP))
 (290 290 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (289 289 (:REWRITE DEFAULT-MOD-2))
 (288 288 (:REWRITE FOLD-CONSTS-IN-+))
 (288 288 (:REWRITE |(< (+ c/d x) y)|))
 (288 288 (:REWRITE |(< (+ (- c) x) y)|))
 (287 287
      (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (287 287
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (287 287 (:REWRITE |(mod x (- y))| . 3))
 (287 287 (:REWRITE |(mod x (- y))| . 2))
 (287 287 (:REWRITE |(mod x (- y))| . 1))
 (287 287
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (287 287
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (287 287
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (196 196 (:TYPE-PRESCRIPTION BOOLEANP))
 (132 28 (:REWRITE RTL::BITN-BVECP-1))
 (94 94 (:REWRITE RATIONALP-MINUS-X))
 (92 92 (:REWRITE REDUCE-RATIONALP-+))
 (92 92 (:META META-RATIONALP-CORRECT))
 (62 62 (:REWRITE ZP-OPEN))
 (58 58 (:REWRITE SUBSETP-MEMBER . 4))
 (58 58 (:REWRITE SUBSETP-MEMBER . 3))
 (58 58 (:REWRITE SUBSETP-MEMBER . 2))
 (58 58 (:REWRITE SUBSETP-MEMBER . 1))
 (58 58 (:REWRITE INTERSECTP-MEMBER . 3))
 (58 58 (:REWRITE INTERSECTP-MEMBER . 2))
 (56 56
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (56 56 (:REWRITE |(+ 0 x)|))
 (56 56 (:LINEAR RTL::MOD-BND-3))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R0-REWRITE
 (418 46 (:REWRITE ACL2-NUMBERP-X))
 (318 19
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (246 22 (:REWRITE ZP-OPEN))
 (213
  213
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (213
     213
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (188 114 (:REWRITE DEFAULT-PLUS-1))
 (186 45 (:REWRITE RATIONALP-X))
 (179 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (131 19 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (111 29 (:REWRITE DEFAULT-MINUS))
 (70 14 (:REWRITE |(+ c (+ d x))|))
 (61 61
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (61 61 (:REWRITE NORMALIZE-ADDENDS))
 (57 57 (:REWRITE REDUCE-INTEGERP-+))
 (57 57 (:REWRITE INTEGERP-MINUS-X))
 (57 57 (:META META-INTEGERP-CORRECT))
 (45 45 (:REWRITE REDUCE-RATIONALP-+))
 (45 45 (:REWRITE REDUCE-RATIONALP-*))
 (45 45 (:REWRITE RATIONALP-MINUS-X))
 (45 45 (:META META-RATIONALP-CORRECT))
 (42 7 (:REWRITE |(- (+ x y))|))
 (39 21
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (39 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (34 34 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (32 32
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (32 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (30 30 (:TYPE-PRESCRIPTION BOOLEANP))
 (28 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (21 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (- x))|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (21 21 (:REWRITE |(< (- x) c)|))
 (21 21 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (19 19 (:REWRITE |(equal c (/ x))|))
 (19 19 (:REWRITE |(equal c (- x))|))
 (19 19 (:REWRITE |(equal (/ x) c)|))
 (19 19 (:REWRITE |(equal (/ x) (/ y))|))
 (19 19 (:REWRITE |(equal (- x) c)|))
 (19 19 (:REWRITE |(equal (- x) (- y))|))
 (18 18 (:REWRITE SUBSETP-MEMBER . 4))
 (18 18 (:REWRITE SUBSETP-MEMBER . 3))
 (18 18 (:REWRITE SUBSETP-MEMBER . 2))
 (18 18 (:REWRITE SUBSETP-MEMBER . 1))
 (18 18 (:REWRITE INTERSECTP-MEMBER . 3))
 (18 18 (:REWRITE INTERSECTP-MEMBER . 2))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE |(< (if a b c) x)|))
 (6 6 (:REWRITE |(* x (if a b c))|))
 (6 6 (:REWRITE |(* c (* d x))|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5 (:REWRITE |(< x (if a b c))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:REWRITE |(+ (if a b c) x)|))
 (2 2 (:REWRITE |(- (if a b c))|))
 (2 2 (:REWRITE |(* (- x) y)|)))
(RTL::R-RECURRENCE
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::R0-BOUND
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M)
(RTL::MAXK)
(RTL::MAXK-SELECT-DIGIT-D4
     (112 28 (:REWRITE RATIONALP-X))
     (108 12 (:REWRITE ACL2-NUMBERP-X))
     (36 36 (:REWRITE REDUCE-INTEGERP-+))
     (36 36 (:REWRITE INTEGERP-MINUS-X))
     (36 36 (:META META-INTEGERP-CORRECT))
     (36 4
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (36 4
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (36 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (36 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (32 8 (:REWRITE INTEGERP-<-CONSTANT))
     (28 28 (:REWRITE REDUCE-RATIONALP-+))
     (28 28 (:REWRITE REDUCE-RATIONALP-*))
     (28 28 (:REWRITE RATIONALP-MINUS-X))
     (28 28 (:META META-RATIONALP-CORRECT))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (8 8 (:REWRITE |(< (- x) (- y))|)))
(RTL::R-BOUND-INV
 (9329
  9329
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9329
      9329
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9329
     9329
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9329 9329
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8103 8103
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8103 8103
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (7061 1968 (:REWRITE DEFAULT-PLUS-2))
 (4577 1628 (:REWRITE DEFAULT-TIMES-1))
 (3528 1968 (:REWRITE DEFAULT-PLUS-1))
 (2722 651 (:REWRITE SIMPLIFY-SUMS-<))
 (2468 770 (:REWRITE DEFAULT-LESS-THAN-1))
 (2468 340 (:REWRITE ACL2-NUMBERP-X))
 (2400 96 (:REWRITE ZP-OPEN))
 (2084 439 (:REWRITE RATIONALP-X))
 (1867 770 (:REWRITE DEFAULT-LESS-THAN-2))
 (1111 43
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (1079 1079
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1060 43
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (978 716 (:REWRITE INTEGERP-<-CONSTANT))
 (924 716 (:REWRITE CONSTANT-<-INTEGERP))
 (924 403 (:REWRITE DEFAULT-MINUS))
 (888 718
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (840 84
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (798 718
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (790 718
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (770 770 (:REWRITE THE-FLOOR-BELOW))
 (770 770 (:REWRITE THE-FLOOR-ABOVE))
 (760 718 (:REWRITE |(< (- x) (- y))|))
 (738 718 (:REWRITE |(< c (- x))|))
 (718 718
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (718 718
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (718 718
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (718 718
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (718 718
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (718 718
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (718 718 (:REWRITE |(< (/ x) (/ y))|))
 (684 684 (:REWRITE REDUCE-INTEGERP-+))
 (684 684 (:REWRITE INTEGERP-MINUS-X))
 (684 684 (:META META-INTEGERP-CORRECT))
 (556 556
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (439 439 (:REWRITE REDUCE-RATIONALP-+))
 (439 439 (:REWRITE REDUCE-RATIONALP-*))
 (439 439 (:REWRITE RATIONALP-MINUS-X))
 (439 439 (:META META-RATIONALP-CORRECT))
 (412 127 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (380 43
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (380 43
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (286 286 (:REWRITE DEFAULT-EXPT-2))
 (286 286 (:REWRITE DEFAULT-EXPT-1))
 (286 286 (:REWRITE |(expt 1/c n)|))
 (286 286 (:REWRITE |(expt (- x) n)|))
 (252 84 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (188 188 (:REWRITE |(< y (+ (- c) x))|))
 (172 172 (:REWRITE |(< (/ x) 0)|))
 (172 172 (:REWRITE |(< (* x y) 0)|))
 (168 168 (:TYPE-PRESCRIPTION BOOLEANP))
 (158 84 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (144 144
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (144 144
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (130 130
      (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (130 130
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (109 109 (:REWRITE |(< (+ c/d x) y)|))
 (109 109 (:REWRITE |(< (+ (- c) x) y)|))
 (84 84
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (84 84 (:REWRITE |(equal c (/ x))|))
 (84 84 (:REWRITE |(equal c (- x))|))
 (84 84 (:REWRITE |(equal (/ x) c)|))
 (84 84 (:REWRITE |(equal (/ x) (/ y))|))
 (84 84 (:REWRITE |(equal (- x) c)|))
 (84 84 (:REWRITE |(equal (- x) (- y))|))
 (76 76 (:REWRITE |(< 0 (/ x))|))
 (76 76 (:REWRITE |(< 0 (* x y))|))
 (76 56
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (74 74
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (74 74
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (72 36
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (56 56
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (56 56
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (56 56
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (52 52 (:REWRITE FOLD-CONSTS-IN-+))
 (36 36
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (36 36
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (36 36
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (34 34 (:REWRITE |(* (- x) y)|))
 (6 6 (:REWRITE SUBSETP-MEMBER . 4))
 (6 6 (:REWRITE SUBSETP-MEMBER . 3))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 3))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(* x (if a b c))|)))
(RTL::DIV123
 (1614 102 (:REWRITE RTL::BVECP-BITN-0))
 (1020 102 (:REWRITE RTL::NEG-BITN-0))
 (246 148 (:REWRITE DEFAULT-TIMES-2))
 (170
   170
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (170
  170
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (170 170
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (170
     170
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (170 170
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (170 170
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (150 148 (:REWRITE DEFAULT-TIMES-1))
 (116 114 (:REWRITE DEFAULT-LESS-THAN-1))
 (114 114 (:REWRITE THE-FLOOR-BELOW))
 (114 114 (:REWRITE THE-FLOOR-ABOVE))
 (114 114 (:REWRITE DEFAULT-LESS-THAN-2))
 (106 90
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (102 102 (:REWRITE RTL::NEG-BITN-1))
 (102 102 (:REWRITE RTL::BITN-NEG))
 (92 90
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (92 90 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (90 90 (:REWRITE SIMPLIFY-SUMS-<))
 (90 90
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (90 90 (:REWRITE INTEGERP-<-CONSTANT))
 (90 90 (:REWRITE CONSTANT-<-INTEGERP))
 (90 90
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (90 90
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (90 90
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (90 90
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (90 90 (:REWRITE |(< c (- x))|))
 (90 90
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (90 90
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (90 90
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (90 90
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (90 90 (:REWRITE |(< (/ x) (/ y))|))
 (90 90 (:REWRITE |(< (- x) c)|))
 (90 90 (:REWRITE |(< (- x) (- y))|))
 (72 72
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (48 32 (:REWRITE DEFAULT-PLUS-1))
 (36 32 (:REWRITE DEFAULT-PLUS-2))
 (29 16
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 16 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (22 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (19 19 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (19 19 (:REWRITE RTL::BITS-NEG-INDICES))
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
 (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::DIV123-D
 (55 19 (:REWRITE DEFAULT-TIMES-2))
 (46 4 (:REWRITE ACL2-NUMBERP-X))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (21 3 (:REWRITE RATIONALP-X))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3L))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2L))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1L))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 1 (:REWRITE DEFAULT-PLUS-2))
 (2 1 (:REWRITE DEFAULT-PLUS-1))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS)))
(RTL::BVECP-DIV1
 (87 6 (:REWRITE RTL::BVECP-BITN-0))
 (60 6 (:REWRITE RTL::NEG-BITN-0))
 (39 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (32 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 13 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (25 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (18 10 (:REWRITE DEFAULT-TIMES-2))
 (16
   16
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (16
  16
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE CONSTANT-<-INTEGERP))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< c (- x))|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE RTL::NEG-BITN-1))
 (6 6 (:REWRITE RTL::BITN-NEG))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BVECP-DIV2
 (88 7 (:REWRITE RTL::BVECP-BITN-0))
 (70 7 (:REWRITE RTL::NEG-BITN-0))
 (42 16 (:REWRITE DEFAULT-LESS-THAN-1))
 (39 15
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (39 15 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (17 11
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE THE-FLOOR-BELOW))
 (16 16 (:REWRITE THE-FLOOR-ABOVE))
 (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
 (15
   15
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (15
  15
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (15 15 (:REWRITE |(equal (- x) c)|))
 (15 15 (:REWRITE |(equal (- x) (- y))|))
 (13 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE SIMPLIFY-SUMS-<))
 (11 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (9 5 (:REWRITE DEFAULT-TIMES-2))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7 (:REWRITE RTL::NEG-BITN-1))
 (7 7 (:REWRITE RTL::BITN-NEG))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::DIVCAR-REWRITE-1 (21 2 (:REWRITE DEFAULT-LOGIOR-2))
                       (15 5
                           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
                       (10 2 (:REWRITE DEFAULT-LOGIOR-1))
                       (10 1
                           (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
                       (6 3 (:REWRITE DEFAULT-LOGAND-2))
                       (6 3 (:REWRITE DEFAULT-LOGAND-1))
                       (5 5 (:TYPE-PRESCRIPTION RTL::DIV1))
                       (5 5
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                       (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
                       (2 2
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                       (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
                       (1 1
                          (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
                       (1 1
                          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
                       (1 1
                          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
                       (1 1 (:REWRITE |(logior c d x)|)))
(RTL::DIVCAR-REWRITE
 (3335 23 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (2672 57
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2594 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (1374 1374
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (438 438
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (438 438
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (438 438
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (426 41 (:REWRITE DEFAULT-LOGIOR-2))
 (394 23 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (301 13 (:REWRITE DEFAULT-TIMES-2))
 (267 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (265 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (248 57 (:REWRITE DEFAULT-LESS-THAN-1))
 (240 3 (:REWRITE |(* y (* x z))|))
 (230 115 (:REWRITE DEFAULT-LOGAND-2))
 (230 115 (:REWRITE DEFAULT-LOGAND-1))
 (205 41 (:REWRITE DEFAULT-LOGIOR-1))
 (188 30 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (188 30 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (188 1 (:REWRITE RTL::LOGIOR-BVECP))
 (149 57 (:REWRITE DEFAULT-LESS-THAN-2))
 (115 115 (:REWRITE LOGAND-CONSTANT-MASK))
 (72 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (72 3 (:REWRITE |(* a (/ a) b)|))
 (65 65 (:REWRITE THE-FLOOR-BELOW))
 (65 65 (:REWRITE THE-FLOOR-ABOVE))
 (54 54 (:REWRITE SIMPLIFY-SUMS-<))
 (54 54
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (54 54
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (54 54 (:REWRITE INTEGERP-<-CONSTANT))
 (54 54 (:REWRITE CONSTANT-<-INTEGERP))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< c (- x))|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) c)|))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (36 13 (:REWRITE DEFAULT-TIMES-1))
 (36 1 (:REWRITE RTL::LOGAND-BVECP))
 (28 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 25 (:REWRITE |(< (/ x) 0)|))
 (25 25 (:REWRITE |(< (* x y) 0)|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< 0 (/ x))|))
 (23 23 (:REWRITE |(< 0 (* x y))|))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (20 20 (:REWRITE |(logior c d x)|))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 3
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::NATP-DIV123
 (130 13 (:REWRITE RTL::NEG-BITN-0))
 (71 28
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (71 28 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (36 20 (:REWRITE DEFAULT-TIMES-2))
 (35 13 (:REWRITE RTL::BVECP-BITN-0))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (28 28 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 28
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (28 28
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (28 28
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (28 28 (:REWRITE |(equal c (/ x))|))
 (28 28 (:REWRITE |(equal c (- x))|))
 (28 28 (:REWRITE |(equal (/ x) c)|))
 (28 28 (:REWRITE |(equal (/ x) (/ y))|))
 (28 28 (:REWRITE |(equal (- x) c)|))
 (28 28 (:REWRITE |(equal (- x) (- y))|))
 (26
   26
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (26
  26
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (26 26
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (26 26
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (26 26
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (26 26
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (15 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE RTL::NEG-BITN-1))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (13 13 (:REWRITE RTL::BITN-NEG))
 (11 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 1 (:REWRITE RTL::BITS-TAIL)))
(RTL::DIV-REWRITE-1
 (123 123
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (75 75
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (75 75
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (75 75
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (46 4 (:REWRITE DEFAULT-TIMES-2))
 (44 3 (:REWRITE DEFAULT-PLUS-2))
 (43 6 (:REWRITE DEFAULT-LOGIOR-2))
 (35 6 (:REWRITE DEFAULT-LOGIOR-1))
 (23 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (23 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 6 (:REWRITE DEFAULT-LOGAND-2))
 (10 6 (:REWRITE DEFAULT-LOGAND-1))
 (8 4 (:REWRITE DEFAULT-LOGXOR-2))
 (6 6 (:REWRITE LOGAND-CONSTANT-MASK))
 (6 4 (:REWRITE DEFAULT-LOGXOR-1))
 (5 3 (:REWRITE DEFAULT-PLUS-1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE |(logior c d x)|))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
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
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::BVECP-SIGB-56
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::BVECP-DIV123
 (916 24 (:REWRITE RTL::NEG-BITN-0))
 (560 24 (:REWRITE RTL::NEG-BITN-1))
 (490 7 (:REWRITE RTL::BITS-TAIL-GEN))
 (394 51
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (102 51 (:REWRITE DEFAULT-LESS-THAN-1))
 (98 7 (:REWRITE |(* y (* x z))|))
 (93 39
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (93 39 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (88 32 (:REWRITE DEFAULT-TIMES-2))
 (81 44
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (81 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (68 24 (:REWRITE RTL::BVECP-BITN-0))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (51 51 (:REWRITE THE-FLOOR-ABOVE))
 (51 51 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 44 (:REWRITE SIMPLIFY-SUMS-<))
 (44 44
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (44 44
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (44 44 (:REWRITE INTEGERP-<-CONSTANT))
 (44 44 (:REWRITE CONSTANT-<-INTEGERP))
 (44 44
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (44 44
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (44 44
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (44 44
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (44 44 (:REWRITE |(< c (- x))|))
 (44 44
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (44 44
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (44 44
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (44 44
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (44 44 (:REWRITE |(< (/ x) (/ y))|))
 (44 44 (:REWRITE |(< (- x) c)|))
 (44 44 (:REWRITE |(< (- x) (- y))|))
 (40
   40
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (40
  40
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (39 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (39 39
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (39 39
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (39 39
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (39 39 (:REWRITE |(equal c (/ x))|))
 (39 39 (:REWRITE |(equal c (- x))|))
 (39 39 (:REWRITE |(equal (/ x) c)|))
 (39 39 (:REWRITE |(equal (/ x) (/ y))|))
 (39 39 (:REWRITE |(equal (- x) c)|))
 (39 39 (:REWRITE |(equal (- x) (- y))|))
 (36 32 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE RTL::BITN-NEG))
 (21 7 (:REWRITE RTL::BITS-TAIL))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (14 14
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (14 7 (:REWRITE |(* a (/ a) b)|))
 (7 7
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7 7 (:TYPE-PRESCRIPTION ABS))
 (7 7 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (7 7 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BVECP-DIVSUMCAR
 (2172 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (1172 10
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (868 6 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (806 6 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (678 2 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (295 295
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (154 6 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (138 12 (:LINEAR RTL::LOGAND-BND))
 (114 6 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (105 10 (:REWRITE DEFAULT-LOGIOR-2))
 (102 6 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (101 5 (:REWRITE DEFAULT-TIMES-2))
 (87 87
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (87 87
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (87 87
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (80 1 (:REWRITE |(* y (* x z))|))
 (58 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (58 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (58 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (50 25 (:REWRITE DEFAULT-LOGAND-2))
 (50 25 (:REWRITE DEFAULT-LOGAND-1))
 (50 10 (:REWRITE DEFAULT-LOGIOR-1))
 (34 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 5 (:REWRITE DEFAULT-TIMES-1))
 (25 25 (:REWRITE LOGAND-CONSTANT-MASK))
 (24 6 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (24 6 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (24 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (24 1 (:REWRITE |(* a (/ a) b)|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(logior c d x)|))
 (4 2 (:REWRITE DEFAULT-LOGXOR-2))
 (4 2 (:REWRITE DEFAULT-LOGXOR-1))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::DIV-REWRITE-2
 (89 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (18 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< c (- x))|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (10 6 (:REWRITE DEFAULT-PLUS-1))
 (9 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 6 (:REWRITE DEFAULT-PLUS-2))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::DIV-REWRITE
 (8 4 (:REWRITE DEFAULT-PLUS-2))
 (8 4 (:REWRITE DEFAULT-PLUS-1))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 1 (:REWRITE DEFAULT-TIMES-2))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE DEFAULT-TIMES-1))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SIGA-BOUNDS
 (8 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (4 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM123
 (4071 102 (:REWRITE RTL::BVECP-BITN-0))
 (2671 102 (:REWRITE RTL::NEG-BITN-0))
 (1240 102 (:REWRITE RTL::NEG-BITN-1))
 (439 279 (:REWRITE DEFAULT-LESS-THAN-1))
 (338 255
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (338 255
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (279 279 (:REWRITE THE-FLOOR-BELOW))
 (279 279 (:REWRITE THE-FLOOR-ABOVE))
 (279 279 (:REWRITE DEFAULT-LESS-THAN-2))
 (271 255
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (255 255 (:REWRITE SIMPLIFY-SUMS-<))
 (255 255
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (255 255 (:REWRITE INTEGERP-<-CONSTANT))
 (255 255 (:REWRITE CONSTANT-<-INTEGERP))
 (255 255
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (255 255
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (255 255
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (255 255
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (255 255 (:REWRITE |(< c (- x))|))
 (255 255
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (255 255
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (255 255
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (255 255
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (255 255 (:REWRITE |(< (/ x) (/ y))|))
 (255 255 (:REWRITE |(< (- x) c)|))
 (255 255 (:REWRITE |(< (- x) (- y))|))
 (246 148 (:REWRITE DEFAULT-TIMES-2))
 (150 148 (:REWRITE DEFAULT-TIMES-1))
 (131
   131
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (131
  131
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (131 131
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (131
     131
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (131 131
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (131 131
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (103 103
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (103 103
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (103 103 (:REWRITE |(< (/ x) 0)|))
 (103 103 (:REWRITE |(< (* x y) 0)|))
 (102 102 (:REWRITE RTL::BITN-NEG))
 (73 73 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (72 72
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (48 32 (:REWRITE DEFAULT-PLUS-1))
 (36 32 (:REWRITE DEFAULT-PLUS-2))
 (29 16
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 16 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (22 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (19 19 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (19 19 (:REWRITE RTL::BITS-NEG-INDICES))
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
 (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::REM123-X
 (90 6 (:REWRITE ACL2-NUMBERP-X))
 (64 23 (:REWRITE DEFAULT-TIMES-2))
 (42 6 (:REWRITE RATIONALP-X))
 (11 11
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 3 (:REWRITE SIMPLIFY-SUMS-<))
 (8 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 6 (:META META-INTEGERP-CORRECT))
 (6 3 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 3 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE THE-FLOOR-BELOW))
 (3 3 (:REWRITE THE-FLOOR-ABOVE))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3 3
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3 3 (:REWRITE INTEGERP-<-CONSTANT))
 (3 3 (:REWRITE CONSTANT-<-INTEGERP))
 (3 3
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3 3
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3 3
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3 3
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< c (- x))|))
 (3 3
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3 3
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3 3
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3 3
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< (/ x) (/ y))|))
 (3 3 (:REWRITE |(< (- x) c)|))
 (3 3 (:REWRITE |(< (- x) (- y))|))
 (2 1 (:REWRITE DEFAULT-PLUS-2))
 (2 1 (:REWRITE DEFAULT-PLUS-1))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS)))
(RTL::BVECP-REM1
 (384 6 (:REWRITE RTL::BVECP-BITN-0))
 (246 6 (:REWRITE RTL::NEG-BITN-0))
 (104 104
      (:TYPE-PRESCRIPTION RTL::INTEGERP-SIGB))
 (76 6 (:REWRITE RTL::NEG-BITN-1))
 (70 36 (:REWRITE DEFAULT-LESS-THAN-1))
 (42 30
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (36 36 (:REWRITE THE-FLOOR-BELOW))
 (36 36 (:REWRITE THE-FLOOR-ABOVE))
 (36 36 (:REWRITE DEFAULT-LESS-THAN-2))
 (36 30
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 13 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (30 30 (:REWRITE SIMPLIFY-SUMS-<))
 (30 30
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (30 30 (:REWRITE INTEGERP-<-CONSTANT))
 (30 30 (:REWRITE CONSTANT-<-INTEGERP))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< c (- x))|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< (/ x) (/ y))|))
 (30 30 (:REWRITE |(< (- x) c)|))
 (30 30 (:REWRITE |(< (- x) (- y))|))
 (18 10 (:REWRITE DEFAULT-TIMES-2))
 (16
   16
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (16
  16
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE RTL::BITN-NEG))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BVECP-REM2
 (322 7 (:REWRITE RTL::BVECP-BITN-0))
 (208 7 (:REWRITE RTL::NEG-BITN-0))
 (90 90
     (:TYPE-PRESCRIPTION RTL::INTEGERP-SIGB))
 (77 7 (:REWRITE RTL::NEG-BITN-1))
 (68 30 (:REWRITE DEFAULT-LESS-THAN-1))
 (39 15
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (39 15 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (31 25
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (31 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30 30 (:REWRITE THE-FLOOR-BELOW))
 (30 30 (:REWRITE THE-FLOOR-ABOVE))
 (30 30 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 25 (:REWRITE SIMPLIFY-SUMS-<))
 (25 25
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (15 15 (:REWRITE |(equal (- x) c)|))
 (15 15 (:REWRITE |(equal (- x) (- y))|))
 (13
   13
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (13
  13
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (9 5 (:REWRITE DEFAULT-TIMES-2))
 (7 7 (:REWRITE RTL::BITN-NEG))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::REMCAR-REWRITE-1 (21 2 (:REWRITE DEFAULT-LOGIOR-2))
                       (15 5
                           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
                       (10 2 (:REWRITE DEFAULT-LOGIOR-1))
                       (10 1
                           (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
                       (6 3 (:REWRITE DEFAULT-LOGAND-2))
                       (6 3 (:REWRITE DEFAULT-LOGAND-1))
                       (5 5 (:TYPE-PRESCRIPTION RTL::REM1))
                       (5 5
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                       (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
                       (2 2
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                       (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
                       (1 1
                          (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
                       (1 1
                          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
                       (1 1
                          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
                       (1 1 (:REWRITE |(logior c d x)|)))
(RTL::REMCAR-REWRITE
 (3335 23 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (2672 57
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2594 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (1374 1374
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (438 438
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (438 438
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (438 438
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (426 41 (:REWRITE DEFAULT-LOGIOR-2))
 (394 23 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (301 13 (:REWRITE DEFAULT-TIMES-2))
 (267 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (265 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (248 57 (:REWRITE DEFAULT-LESS-THAN-1))
 (240 3 (:REWRITE |(* y (* x z))|))
 (230 115 (:REWRITE DEFAULT-LOGAND-2))
 (230 115 (:REWRITE DEFAULT-LOGAND-1))
 (205 41 (:REWRITE DEFAULT-LOGIOR-1))
 (188 30 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (188 30 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (188 1 (:REWRITE RTL::LOGIOR-BVECP))
 (149 57 (:REWRITE DEFAULT-LESS-THAN-2))
 (115 115 (:REWRITE LOGAND-CONSTANT-MASK))
 (72 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (72 3 (:REWRITE |(* a (/ a) b)|))
 (65 65 (:REWRITE THE-FLOOR-BELOW))
 (65 65 (:REWRITE THE-FLOOR-ABOVE))
 (54 54 (:REWRITE SIMPLIFY-SUMS-<))
 (54 54
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (54 54
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (54 54 (:REWRITE INTEGERP-<-CONSTANT))
 (54 54 (:REWRITE CONSTANT-<-INTEGERP))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< c (- x))|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) c)|))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (36 13 (:REWRITE DEFAULT-TIMES-1))
 (36 1 (:REWRITE RTL::LOGAND-BVECP))
 (28 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 25 (:REWRITE |(< (/ x) 0)|))
 (25 25 (:REWRITE |(< (* x y) 0)|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< 0 (/ x))|))
 (23 23 (:REWRITE |(< 0 (* x y))|))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (20 20 (:REWRITE |(logior c d x)|))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 3
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::NATP-REM123
 (454 13 (:REWRITE RTL::NEG-BITN-0))
 (153 13 (:REWRITE RTL::NEG-BITN-1))
 (106 106
      (:TYPE-PRESCRIPTION RTL::INTEGERP-SIGB))
 (71 28
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (71 28 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (45 28 (:REWRITE DEFAULT-LESS-THAN-1))
 (36 20 (:REWRITE DEFAULT-TIMES-2))
 (35 13 (:REWRITE RTL::BVECP-BITN-0))
 (34 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (34 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (28 28 (:REWRITE THE-FLOOR-BELOW))
 (28 28 (:REWRITE THE-FLOOR-ABOVE))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (28 28 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 28
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (28 28
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (28 28
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (28 28 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 28 (:REWRITE |(equal c (/ x))|))
 (28 28 (:REWRITE |(equal c (- x))|))
 (28 28 (:REWRITE |(equal (/ x) c)|))
 (28 28 (:REWRITE |(equal (/ x) (/ y))|))
 (28 28 (:REWRITE |(equal (- x) c)|))
 (28 28 (:REWRITE |(equal (- x) (- y))|))
 (24
   24
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24 (:REWRITE SIMPLIFY-SUMS-<))
 (24 24
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (24 24 (:REWRITE INTEGERP-<-CONSTANT))
 (24 24 (:REWRITE CONSTANT-<-INTEGERP))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< c (- x))|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< (/ x) (/ y))|))
 (24 24 (:REWRITE |(< (- x) c)|))
 (24 24 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (13 13 (:REWRITE RTL::BITN-NEG))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 1 (:REWRITE RTL::BITS-TAIL)))
(RTL::REM-REWRITE-1
 (151 151
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (89 89
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (89 89
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (89 89
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (71 7 (:REWRITE DEFAULT-TIMES-2))
 (69 10 (:REWRITE DEFAULT-LOGIOR-2))
 (65 4 (:REWRITE DEFAULT-PLUS-2))
 (61 10 (:REWRITE DEFAULT-LOGIOR-1))
 (30 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (30 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (15 9 (:REWRITE DEFAULT-LOGAND-2))
 (15 9 (:REWRITE DEFAULT-LOGAND-1))
 (12 6 (:REWRITE DEFAULT-LOGXOR-2))
 (10 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE LOGAND-CONSTANT-MASK))
 (9 6 (:REWRITE DEFAULT-LOGXOR-1))
 (9 4 (:REWRITE SIMPLIFY-SUMS-<))
 (9 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (7 4 (:REWRITE DEFAULT-PLUS-1))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:REWRITE |(logior c d x)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
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
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::BVECP-SIGA-56
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::BVECP-REM123
 (916 24 (:REWRITE RTL::NEG-BITN-0))
 (560 24 (:REWRITE RTL::NEG-BITN-1))
 (490 7 (:REWRITE RTL::BITS-TAIL-GEN))
 (394 51
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (102 51 (:REWRITE DEFAULT-LESS-THAN-1))
 (98 7 (:REWRITE |(* y (* x z))|))
 (93 39
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (93 39 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (88 32 (:REWRITE DEFAULT-TIMES-2))
 (81 44
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (81 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (68 24 (:REWRITE RTL::BVECP-BITN-0))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (51 51 (:REWRITE THE-FLOOR-ABOVE))
 (51 51 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 44 (:REWRITE SIMPLIFY-SUMS-<))
 (44 44
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (44 44
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (44 44 (:REWRITE INTEGERP-<-CONSTANT))
 (44 44 (:REWRITE CONSTANT-<-INTEGERP))
 (44 44
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (44 44
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (44 44
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (44 44
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (44 44 (:REWRITE |(< c (- x))|))
 (44 44
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (44 44
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (44 44
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (44 44
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (44 44 (:REWRITE |(< (/ x) (/ y))|))
 (44 44 (:REWRITE |(< (- x) c)|))
 (44 44 (:REWRITE |(< (- x) (- y))|))
 (40
   40
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (40
  40
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (39 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (39 39
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (39 39
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (39 39
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (39 39 (:REWRITE |(equal c (/ x))|))
 (39 39 (:REWRITE |(equal c (- x))|))
 (39 39 (:REWRITE |(equal (/ x) c)|))
 (39 39 (:REWRITE |(equal (/ x) (/ y))|))
 (39 39 (:REWRITE |(equal (- x) c)|))
 (39 39 (:REWRITE |(equal (- x) (- y))|))
 (36 32 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE RTL::BITN-NEG))
 (21 7 (:REWRITE RTL::BITS-TAIL))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (14 14
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (14 7 (:REWRITE |(* a (/ a) b)|))
 (7 7
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7 7 (:TYPE-PRESCRIPTION ABS))
 (7 7 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (7 7 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BVECP-REMSUMCAR
 (2172 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (1172 10
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (868 6 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (806 6 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (678 2 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (295 295
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (154 6 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (138 12 (:LINEAR RTL::LOGAND-BND))
 (114 6 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (105 10 (:REWRITE DEFAULT-LOGIOR-2))
 (102 6 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (101 5 (:REWRITE DEFAULT-TIMES-2))
 (87 87
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (87 87
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (87 87
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (80 1 (:REWRITE |(* y (* x z))|))
 (58 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (58 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (58 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (50 25 (:REWRITE DEFAULT-LOGAND-2))
 (50 25 (:REWRITE DEFAULT-LOGAND-1))
 (50 10 (:REWRITE DEFAULT-LOGIOR-1))
 (34 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 5 (:REWRITE DEFAULT-TIMES-1))
 (25 25 (:REWRITE LOGAND-CONSTANT-MASK))
 (24 6 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (24 6 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (24 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (24 1 (:REWRITE |(* a (/ a) b)|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(logior c d x)|))
 (4 2 (:REWRITE DEFAULT-LOGXOR-2))
 (4 2 (:REWRITE DEFAULT-LOGXOR-1))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::SIGALTSIGB-REWRITE
 (696 7 (:REWRITE RTL::NEG-BITN-0))
 (501 7 (:REWRITE RTL::NEG-BITN-1))
 (428 385 (:REWRITE DEFAULT-PLUS-1))
 (391 385 (:REWRITE DEFAULT-PLUS-2))
 (280 28 (:REWRITE |(< y (+ (- c) x))|))
 (172 80 (:REWRITE |(< (+ (- c) x) y)|))
 (134 134
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (122 111 (:REWRITE DEFAULT-LESS-THAN-1))
 (111 111 (:REWRITE THE-FLOOR-BELOW))
 (111 111 (:REWRITE THE-FLOOR-ABOVE))
 (111 111
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (111 111
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (111 111 (:REWRITE DEFAULT-LESS-THAN-2))
 (108 98
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (104 103
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (103 103
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (103 103
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (103 103
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (103 103
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (103 103 (:REWRITE |(< c (- x))|))
 (103 103
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (103 103
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (103 103
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (103 103 (:REWRITE |(< (/ x) (/ y))|))
 (103 103 (:REWRITE |(< (- x) (- y))|))
 (100 98
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (98 98 (:REWRITE INTEGERP-<-CONSTANT))
 (98 98 (:REWRITE CONSTANT-<-INTEGERP))
 (86 86 (:REWRITE |(< (+ c/d x) y)|))
 (62 62 (:REWRITE SIMPLIFY-SUMS-<))
 (55
   55
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (55
  55
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (41 37 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (28 28 (:REWRITE |(< x (+ c/d y))|))
 (26 26 (:REWRITE DEFAULT-MINUS))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (16 16 (:REWRITE RTL::BITS-NEG-INDICES))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (11 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 3 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE RTL::BITN-NEG))
 (4 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE RTL::BITS-BITS-SUM-ALT)))
(RTL::RP-1-REWRITE
 (328 6 (:REWRITE RTL::BITS-TAIL))
 (124 60 (:REWRITE DEFAULT-TIMES-2))
 (86 50 (:REWRITE DEFAULT-LESS-THAN-1))
 (66 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (65 34
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (62 60 (:REWRITE DEFAULT-TIMES-1))
 (58 50 (:REWRITE DEFAULT-LESS-THAN-2))
 (56 4 (:REWRITE |(* y (* x z))|))
 (50 50 (:REWRITE THE-FLOOR-BELOW))
 (50 50 (:REWRITE THE-FLOOR-ABOVE))
 (46 36
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (44 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (43 34 (:REWRITE SIMPLIFY-SUMS-<))
 (38 36
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (36 36 (:REWRITE INTEGERP-<-CONSTANT))
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
 (35 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 12 (:REWRITE DEFAULT-PLUS-1))
 (18 12 (:REWRITE DEFAULT-PLUS-2))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (9 9 (:REWRITE RTL::BITS-NEG-INDICES))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 4 (:REWRITE |(* a (/ a) b)|))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::A-1 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::INTEGERP-8*A-1 (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (9 3 (:REWRITE DEFAULT-TIMES-2))
                     (4 3 (:REWRITE DEFAULT-TIMES-1))
                     (2 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (1 1
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::A-1-1
 (5052 132 (:REWRITE RTL::BITS-TAIL-GEN))
 (916 30 (:REWRITE RTL::BVECP-BITN-0))
 (731 418 (:REWRITE DEFAULT-LESS-THAN-1))
 (687 390
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (582 312 (:REWRITE DEFAULT-PLUS-2))
 (474 418 (:REWRITE DEFAULT-LESS-THAN-2))
 (471 312 (:REWRITE DEFAULT-PLUS-1))
 (452 378 (:REWRITE SIMPLIFY-SUMS-<))
 (450 414
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (418 418 (:REWRITE THE-FLOOR-BELOW))
 (418 418 (:REWRITE THE-FLOOR-ABOVE))
 (418 414 (:REWRITE |(< (- x) (- y))|))
 (414 414
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (414 414
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (414 414
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (414 414
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (414 414
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (414 414
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (414 414 (:REWRITE |(< c (- x))|))
 (414 414
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (414 414
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (414 414
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (414 414 (:REWRITE |(< (/ x) (/ y))|))
 (406 406 (:REWRITE INTEGERP-<-CONSTANT))
 (406 406 (:REWRITE CONSTANT-<-INTEGERP))
 (320 30 (:REWRITE RTL::NEG-BITN-0))
 (252 112 (:REWRITE DEFAULT-TIMES-2))
 (244
   244
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (244
  244
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (244 244
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (244
     244
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (244 244
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (244 244
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (228 228
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (228 228 (:REWRITE RTL::BITS-NEG-INDICES))
 (189 70
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (179 179
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (170 70 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (129 70 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (112 112 (:REWRITE DEFAULT-TIMES-1))
 (109 68 (:REWRITE DEFAULT-MINUS))
 (100 100
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (70 70
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (70 70
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (70 70
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (70 70 (:REWRITE |(equal c (/ x))|))
 (70 70 (:REWRITE |(equal c (- x))|))
 (70 70 (:REWRITE |(equal (/ x) c)|))
 (70 70 (:REWRITE |(equal (/ x) (/ y))|))
 (70 70 (:REWRITE |(equal (- x) c)|))
 (70 70 (:REWRITE |(equal (- x) (- y))|))
 (60 60 (:REWRITE |(< (+ c/d x) y)|))
 (60 60 (:REWRITE |(< (+ (- c) x) y)|))
 (50 30 (:REWRITE RTL::NEG-BITN-1))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (36 36 (:REWRITE |(equal (+ (- c) x) y)|))
 (36 36 (:REWRITE |(< y (+ (- c) x))|))
 (36 36 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE RTL::BITN-NEG))
 (24 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE |(* (- x) y)|))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|)))
(RTL::A-1-2
 (319 172 (:REWRITE DEFAULT-PLUS-2))
 (319 172 (:REWRITE DEFAULT-PLUS-1))
 (138 47 (:REWRITE DEFAULT-LESS-THAN-1))
 (115 59 (:REWRITE DEFAULT-TIMES-2))
 (107 40
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (77 33 (:REWRITE DEFAULT-MINUS))
 (73 47 (:REWRITE DEFAULT-LESS-THAN-2))
 (64 42
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (64 25 (:REWRITE SIMPLIFY-SUMS-<))
 (59 59 (:REWRITE DEFAULT-TIMES-1))
 (47 47 (:REWRITE THE-FLOOR-BELOW))
 (47 47 (:REWRITE THE-FLOOR-ABOVE))
 (46 42 (:REWRITE |(< (- x) (- y))|))
 (46 23 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (44 44
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (42 42
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (42 42
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (42 42
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (42 42
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (42 42 (:REWRITE |(< c (- x))|))
 (42 42
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (42 42
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (42 42
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (42 42
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (42 42 (:REWRITE |(< (/ x) (/ y))|))
 (40 40 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 40
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (40 40 (:REWRITE INTEGERP-<-CONSTANT))
 (40 40 (:REWRITE CONSTANT-<-INTEGERP))
 (31 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (31 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29
   29
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (29
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:REWRITE |(+ c (+ d x))|))
 (13 13 (:REWRITE |(< y (+ (- c) x))|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(* (- x) y)|))
 (7 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::A-1-3
 (704 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (678 4
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (346 135 (:REWRITE DEFAULT-PLUS-2))
 (286 135 (:REWRITE DEFAULT-PLUS-1))
 (260 8 (:REWRITE |(* x (+ y z))|))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (196 66 (:REWRITE DEFAULT-TIMES-2))
 (187 40 (:REWRITE DEFAULT-LESS-THAN-1))
 (142 36
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (127 37 (:REWRITE INTEGERP-<-CONSTANT))
 (92 66 (:REWRITE DEFAULT-TIMES-1))
 (74 19 (:REWRITE SIMPLIFY-SUMS-<))
 (68 40 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 20 (:REWRITE DEFAULT-MINUS))
 (52 4 (:REWRITE |(* x (- y))|))
 (46 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (45 37 (:REWRITE |(< (- x) c)|))
 (45 37 (:REWRITE |(< (- x) (- y))|))
 (43 43
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (40 40 (:REWRITE THE-FLOOR-BELOW))
 (40 40 (:REWRITE THE-FLOOR-ABOVE))
 (39 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (39 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37 (:REWRITE CONSTANT-<-INTEGERP))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< c (- x))|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (32 4 (:REWRITE |(* c (* d x))|))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (26 4
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (26 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (25 25 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE |(* (- x) y)|))
 (12 4 (:REWRITE |(* -1 x)|))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 4 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE |arith (* (- x) y)|))
 (4 4 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::A-1-4
 (916 30 (:REWRITE RTL::BVECP-BITN-0))
 (731 418 (:REWRITE DEFAULT-LESS-THAN-1))
 (687 390
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (582 312 (:REWRITE DEFAULT-PLUS-2))
 (474 418 (:REWRITE DEFAULT-LESS-THAN-2))
 (474 406
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (471 312 (:REWRITE DEFAULT-PLUS-1))
 (452 378 (:REWRITE SIMPLIFY-SUMS-<))
 (450 414
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (418 418 (:REWRITE THE-FLOOR-BELOW))
 (418 418 (:REWRITE THE-FLOOR-ABOVE))
 (418 414 (:REWRITE |(< (- x) (- y))|))
 (414 414
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (414 414
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (414 414
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (414 414
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (414 414
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (414 414
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (414 414 (:REWRITE |(< c (- x))|))
 (414 414
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (414 414
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (414 414
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (414 414 (:REWRITE |(< (/ x) (/ y))|))
 (406 406 (:REWRITE INTEGERP-<-CONSTANT))
 (406 406 (:REWRITE CONSTANT-<-INTEGERP))
 (320 30 (:REWRITE RTL::NEG-BITN-0))
 (260
   260
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (260
  260
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (260 260
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (260
     260
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (260 260
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (260 260
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (252 112 (:REWRITE DEFAULT-TIMES-2))
 (228 228
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (228 228 (:REWRITE RTL::BITS-NEG-INDICES))
 (189 70
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (179 179
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (170 70 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (129 70 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (112 112 (:REWRITE DEFAULT-TIMES-1))
 (109 68 (:REWRITE DEFAULT-MINUS))
 (100 100
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (70 70
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (70 70
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (70 70
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (70 70 (:REWRITE |(equal c (/ x))|))
 (70 70 (:REWRITE |(equal c (- x))|))
 (70 70 (:REWRITE |(equal (/ x) c)|))
 (70 70 (:REWRITE |(equal (/ x) (/ y))|))
 (70 70 (:REWRITE |(equal (- x) c)|))
 (70 70 (:REWRITE |(equal (- x) (- y))|))
 (60 60 (:REWRITE |(< (+ c/d x) y)|))
 (60 60 (:REWRITE |(< (+ (- c) x) y)|))
 (50 30 (:REWRITE RTL::NEG-BITN-1))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (36 36 (:REWRITE |(equal (+ (- c) x) y)|))
 (36 36 (:REWRITE |(< y (+ (- c) x))|))
 (36 36 (:REWRITE |(< x (+ c/d y))|))
 (34 34 (:REWRITE |(< (/ x) 0)|))
 (34 34 (:REWRITE |(< (* x y) 0)|))
 (30 30 (:REWRITE RTL::BITN-NEG))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (24 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12 (:REWRITE |(* (- x) y)|))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|)))
(RTL::A-1-5
 (320 172 (:REWRITE DEFAULT-PLUS-2))
 (318 172 (:REWRITE DEFAULT-PLUS-1))
 (138 47 (:REWRITE DEFAULT-LESS-THAN-1))
 (115 59 (:REWRITE DEFAULT-TIMES-2))
 (106 40
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (77 33 (:REWRITE DEFAULT-MINUS))
 (72 47 (:REWRITE DEFAULT-LESS-THAN-2))
 (64 42
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (63 25 (:REWRITE SIMPLIFY-SUMS-<))
 (59 59 (:REWRITE DEFAULT-TIMES-1))
 (47 47 (:REWRITE THE-FLOOR-BELOW))
 (47 47 (:REWRITE THE-FLOOR-ABOVE))
 (46 42 (:REWRITE |(< (- x) (- y))|))
 (46 23 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (44 44
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (42 42
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (42 42
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (42 42
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (42 42
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (42 42 (:REWRITE |(< c (- x))|))
 (42 42
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (42 42
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (42 42
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (42 42
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (42 42 (:REWRITE |(< (/ x) (/ y))|))
 (40 40 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 40
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (40 40 (:REWRITE INTEGERP-<-CONSTANT))
 (40 40 (:REWRITE CONSTANT-<-INTEGERP))
 (31 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (31 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29
   29
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (29
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:REWRITE |(+ c (+ d x))|))
 (13 13 (:REWRITE |(< y (+ (- c) x))|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(* (- x) y)|))
 (7 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::A-1-6
 (704 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (678 4
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (346 135 (:REWRITE DEFAULT-PLUS-2))
 (286 135 (:REWRITE DEFAULT-PLUS-1))
 (260 8 (:REWRITE |(* x (+ y z))|))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (212 212
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (196 66 (:REWRITE DEFAULT-TIMES-2))
 (187 40 (:REWRITE DEFAULT-LESS-THAN-1))
 (142 36
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (127 37 (:REWRITE INTEGERP-<-CONSTANT))
 (92 66 (:REWRITE DEFAULT-TIMES-1))
 (74 19 (:REWRITE SIMPLIFY-SUMS-<))
 (68 40 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 20 (:REWRITE DEFAULT-MINUS))
 (52 4 (:REWRITE |(* x (- y))|))
 (46 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (45 37 (:REWRITE |(< (- x) c)|))
 (45 37 (:REWRITE |(< (- x) (- y))|))
 (43 43
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (40 40 (:REWRITE THE-FLOOR-BELOW))
 (40 40 (:REWRITE THE-FLOOR-ABOVE))
 (39 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (39 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 37 (:REWRITE CONSTANT-<-INTEGERP))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< c (- x))|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (32 4 (:REWRITE |(* c (* d x))|))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (26 4
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (26 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (25 25 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE |(* (- x) y)|))
 (12 4 (:REWRITE |(* -1 x)|))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 4 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE |arith (* (- x) y)|))
 (4 4 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::A-1-ERROR)
(RTL::BVECP-REMBITS
 (61 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (12 12 (:TYPE-PRESCRIPTION RTL::REMSUMBITS))
 (11 11 (:TYPE-PRESCRIPTION RTL::REMCIN))
 (9 9 (:TYPE-PRESCRIPTION RTL::REMCARBITS))
 (7 3 (:REWRITE DEFAULT-PLUS-2))
 (6 3 (:REWRITE DEFAULT-PLUS-1))
 (4 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
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
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(RTL::Q1-REWRITE
 (744 72 (:REWRITE RTL::NEG-BITN-0))
 (261 261
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (261 261
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (261 261
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (216 72 (:REWRITE RTL::BVECP-BITN-0))
 (102
   102
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (102
  102
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (102 102
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (102
     102
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (102 102
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (102 102
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (100 63
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (99 63 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (96 72 (:REWRITE RTL::NEG-BITN-1))
 (72 72 (:REWRITE RTL::BITN-NEG))
 (69 63 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (63 63
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (63 63
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (63 63
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (63 63 (:REWRITE |(equal c (/ x))|))
 (63 63 (:REWRITE |(equal c (- x))|))
 (63 63 (:REWRITE |(equal (/ x) c)|))
 (63 63 (:REWRITE |(equal (/ x) (/ y))|))
 (63 63 (:REWRITE |(equal (- x) c)|))
 (63 63 (:REWRITE |(equal (- x) (- y))|))
 (63 27 (:REWRITE DEFAULT-PLUS-2))
 (63 27 (:REWRITE DEFAULT-PLUS-1))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (18 9 (:REWRITE DEFAULT-TIMES-2))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 15 (:REWRITE NORMALIZE-ADDENDS))
 (12 4 (:REWRITE RTL::BITN-BVECP-1))
 (9 9 (:REWRITE DEFAULT-TIMES-1))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::A-1-LOWER (397 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
                (384 4
                     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
                (112 4 (:REWRITE |(* x (+ y z))|))
                (101 55 (:REWRITE DEFAULT-PLUS-1))
                (95 55 (:REWRITE DEFAULT-PLUS-2))
                (92 2
                    (:REWRITE |(<= x (/ y)) with (< 0 y)|))
                (82 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
                (81 43 (:REWRITE DEFAULT-TIMES-2))
                (67 32
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (66 32 (:REWRITE INTEGERP-<-CONSTANT))
                (64 33 (:REWRITE DEFAULT-LESS-THAN-1))
                (52 32 (:REWRITE CONSTANT-<-INTEGERP))
                (52 4 (:REWRITE |(* x (- y))|))
                (51 43 (:REWRITE DEFAULT-TIMES-1))
                (48 32
                    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (48 32
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (46 33 (:REWRITE DEFAULT-LESS-THAN-2))
                (37 25 (:REWRITE SIMPLIFY-SUMS-<))
                (36 2 (:REWRITE BUBBLE-DOWN-+-BUBBLE-DOWN))
                (35 32 (:REWRITE |(< (- x) c)|))
                (35 32 (:REWRITE |(< (- x) (- y))|))
                (33 33 (:REWRITE THE-FLOOR-BELOW))
                (33 33 (:REWRITE THE-FLOOR-ABOVE))
                (32 32
                    (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (32 32
                    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                (32 32
                    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                (32 32
                    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                (32 32
                    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                (32 32 (:REWRITE |(< c (- x))|))
                (32 32
                    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                (32 32
                    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                (32 32
                    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                (32 32
                    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                (32 32 (:REWRITE |(< (/ x) (/ y))|))
                (27 27
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (24 4 (:REWRITE |(- (* c x))|))
                (20 4 (:REWRITE |(+ (* c x) (* d x))|))
                (18 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                (15 8 (:REWRITE DEFAULT-MINUS))
                (12 12
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (10 8 (:REWRITE INTEGERP-MINUS-X))
                (9 4
                   (:REWRITE |(<= (/ x) y) with (< x 0)|))
                (9 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
                (8 8 (:REWRITE REDUCE-INTEGERP-+))
                (8 8 (:META META-INTEGERP-CORRECT))
                (7 7 (:REWRITE |(< (+ c/d x) y)|))
                (7 7 (:REWRITE |(< (+ (- c) x) y)|))
                (6 6 (:REWRITE |(< y (+ (- c) x))|))
                (6 6 (:REWRITE |(< x (+ c/d y))|))
                (4 4 (:REWRITE |(* 0 x)|))
                (4 4 (:REWRITE |(* (- x) y)|))
                (4 2
                   (:REWRITE |(<= x (/ y)) with (< y 0)|))
                (4 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
                (3 3 (:REWRITE |(+ c (+ d x))|))
                (2 2 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
                (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                (2 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (1 1 (:REWRITE |(< (/ x) 0)|))
                (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::Q1-MAXK-A-1 (46 1
                      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
                  (41 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
                  (36 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
                  (34 1
                      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
                  (18 8 (:REWRITE INTEGERP-<-CONSTANT))
                  (16 8
                      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                  (16 8
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                  (14 8 (:REWRITE CONSTANT-<-INTEGERP))
                  (11 8
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                  (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                  (11 8 (:REWRITE DEFAULT-LESS-THAN-2))
                  (9 2 (:REWRITE |(* y x)|))
                  (8 8
                     (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
                  (8 8 (:TYPE-PRESCRIPTION ABS))
                  (8 8 (:REWRITE THE-FLOOR-BELOW))
                  (8 8 (:REWRITE THE-FLOOR-ABOVE))
                  (8 8 (:REWRITE SIMPLIFY-SUMS-<))
                  (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                  (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
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
                  (8 6 (:REWRITE DEFAULT-TIMES-2))
                  (7 6 (:REWRITE DEFAULT-TIMES-1))
                  (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                  (4 4
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (3 3 (:REWRITE REDUCE-INTEGERP-+))
                  (3 3 (:REWRITE INTEGERP-MINUS-X))
                  (3 3 (:META META-INTEGERP-CORRECT))
                  (2 1
                     (:REWRITE |(<= x (/ y)) with (< y 0)|))
                  (2 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
                  (1 1
                     (:REWRITE |(<= (/ x) y) with (< x 0)|))
                  (1 1
                     (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::R1-BOUND
     (813 813
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (813 813
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (813 813
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (315 90 (:REWRITE DEFAULT-LESS-THAN-1))
     (266 79
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (248 24 (:REWRITE RATIONALP-X))
     (229 65 (:REWRITE SIMPLIFY-SUMS-<))
     (146 100 (:REWRITE DEFAULT-PLUS-1))
     (137 79 (:REWRITE INTEGERP-<-CONSTANT))
     (132 100 (:REWRITE DEFAULT-PLUS-2))
     (125 90 (:REWRITE DEFAULT-LESS-THAN-2))
     (122 8
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (122 8
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (122 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (122 8 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (90 90 (:REWRITE THE-FLOOR-BELOW))
     (90 90 (:REWRITE THE-FLOOR-ABOVE))
     (84 55 (:REWRITE DEFAULT-TIMES-2))
     (83 79 (:REWRITE |(< (- x) c)|))
     (83 79 (:REWRITE |(< (- x) (- y))|))
     (79 79 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (79 79
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (79 79
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (79 79
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (79 79 (:REWRITE CONSTANT-<-INTEGERP))
     (79 79
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (79 79
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (79 79
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (79 79
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (79 79 (:REWRITE |(< c (- x))|))
     (79 79
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (79 79
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (79 79
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (79 79
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (79 79 (:REWRITE |(< (/ x) (/ y))|))
     (55 55 (:REWRITE DEFAULT-TIMES-1))
     (45 45
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (44 34 (:REWRITE INTEGERP-MINUS-X))
     (41 33 (:REWRITE DEFAULT-MINUS))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:META META-INTEGERP-CORRECT))
     (32 24 (:REWRITE RATIONALP-MINUS-X))
     (30 30
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (30 30
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (27 27 (:REWRITE |(< (/ x) 0)|))
     (27 27 (:REWRITE |(< (* x y) 0)|))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:META META-RATIONALP-CORRECT))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE |(* (- x) y)|))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::BVECP-DIV*
 (53 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (11 11 (:TYPE-PRESCRIPTION RTL::DIVSUM))
 (10 10 (:TYPE-PRESCRIPTION RTL::DIVCAR))
 (4 2 (:REWRITE DEFAULT-PLUS-2))
 (4 2 (:REWRITE DEFAULT-PLUS-1))
 (3 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (3 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
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
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::RN-1-REWRITE-1
 (360 10 (:REWRITE RTL::BVECP-BITN-0))
 (163 17
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (155 6 (:REWRITE RTL::BITS-TAIL-GEN))
 (148 148 (:TYPE-PRESCRIPTION RTL::REMBITS))
 (147 17 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (120 10 (:REWRITE RTL::NEG-BITN-0))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (72 2 (:REWRITE RTL::BITN-BVECP-1))
 (65 18
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 4 (:REWRITE DEFAULT-MOD-RATIO))
 (49 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (38 19 (:REWRITE DEFAULT-TIMES-2))
 (37 19 (:REWRITE DEFAULT-TIMES-1))
 (36 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (33 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (33 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30 10 (:REWRITE RTL::NEG-BITN-1))
 (28 16 (:REWRITE DEFAULT-LOGAND-2))
 (26 16 (:REWRITE DEFAULT-LOGAND-1))
 (20 4 (:REWRITE |(* y x)|))
 (19 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (18 17
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 17 (:REWRITE SIMPLIFY-SUMS-<))
 (17 17
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (17 17 (:REWRITE |(equal c (/ x))|))
 (17 17 (:REWRITE |(equal c (- x))|))
 (17 17 (:REWRITE |(equal (/ x) c)|))
 (17 17 (:REWRITE |(equal (/ x) (/ y))|))
 (17 17 (:REWRITE |(equal (- x) c)|))
 (17 17 (:REWRITE |(equal (- x) (- y))|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< c (- x))|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE |(< (- x) c)|))
 (17 17 (:REWRITE |(< (- x) (- y))|))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 1 (:REWRITE |(* y (* x z))|))
 (11 11
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (10 10 (:REWRITE RTL::BITN-NEG))
 (8 4 (:REWRITE DEFAULT-MOD-1))
 (7 4 (:REWRITE DEFAULT-PLUS-2))
 (6 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
 (5 4 (:REWRITE DEFAULT-PLUS-1))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE DEFAULT-MOD-2))
 (4 4 (:REWRITE |(mod x 2)| . 2))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 1 (:REWRITE |(* a (/ a) b)|))
 (1 1
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::RN-1-REWRITE
 (63 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (63 17
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (60 27 (:REWRITE DEFAULT-TIMES-2))
 (42 27 (:REWRITE DEFAULT-TIMES-1))
 (35 17 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
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
 (6 6 (:REWRITE |(* c (* d x))|))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::RP1-RN1
 (176 65 (:REWRITE DEFAULT-PLUS-2))
 (150 65 (:REWRITE DEFAULT-PLUS-1))
 (94 38 (:REWRITE DEFAULT-TIMES-2))
 (22 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 8 (:REWRITE DEFAULT-MINUS))
 (20 20
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (8 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE |(* c (* d x))|))
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:REWRITE |(* (- x) y)|))
 (2 2
    (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:META META-RATIONALP-CORRECT))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE |(equal (* x y) 0)|)))
(RTL::P-VALS (30 3
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (27 3 (:REWRITE ACL2-NUMBERP-X))
             (12 3 (:REWRITE RATIONALP-X))
             (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
             (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
             (4 4 (:REWRITE SUBSETP-MEMBER . 4))
             (4 4 (:REWRITE SUBSETP-MEMBER . 3))
             (4 4 (:REWRITE SUBSETP-MEMBER . 2))
             (4 4 (:REWRITE SUBSETP-MEMBER . 1))
             (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
             (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
             (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (3 3 (:REWRITE REDUCE-RATIONALP-+))
             (3 3 (:REWRITE REDUCE-RATIONALP-*))
             (3 3
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (3 3 (:REWRITE REDUCE-INTEGERP-+))
             (3 3
                (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (3 3 (:REWRITE RATIONALP-MINUS-X))
             (3 3 (:REWRITE INTEGERP-MINUS-X))
             (3 3
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (3 3 (:REWRITE |(equal c (/ x))|))
             (3 3 (:REWRITE |(equal c (- x))|))
             (3 3 (:REWRITE |(equal (/ x) c)|))
             (3 3 (:REWRITE |(equal (/ x) (/ y))|))
             (3 3 (:REWRITE |(equal (- x) c)|))
             (3 3 (:REWRITE |(equal (- x) (- y))|))
             (3 3 (:META META-RATIONALP-CORRECT))
             (3 3 (:META META-INTEGERP-CORRECT))
             (1 1
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::INT-RN-1
 (1768 706 (:REWRITE DEFAULT-TIMES-2))
 (839 706 (:REWRITE DEFAULT-TIMES-1))
 (331 331
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (243 243
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (243 243
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (243 243
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (182 62
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (126 62 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (111 111 (:REWRITE REDUCE-INTEGERP-+))
 (111 111 (:REWRITE INTEGERP-MINUS-X))
 (111 111 (:META META-INTEGERP-CORRECT))
 (98 98 (:REWRITE SUBSETP-MEMBER . 4))
 (98 98 (:REWRITE SUBSETP-MEMBER . 3))
 (98 98 (:REWRITE SUBSETP-MEMBER . 2))
 (98 98 (:REWRITE SUBSETP-MEMBER . 1))
 (98 98 (:REWRITE INTERSECTP-MEMBER . 3))
 (98 98 (:REWRITE INTERSECTP-MEMBER . 2))
 (90 10 (:REWRITE ACL2-NUMBERP-X))
 (62 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (62 62
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (62 62
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (62 62
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (62 62 (:REWRITE |(equal c (/ x))|))
 (62 62 (:REWRITE |(equal c (- x))|))
 (62 62 (:REWRITE |(equal (/ x) c)|))
 (62 62 (:REWRITE |(equal (/ x) (/ y))|))
 (62 62 (:REWRITE |(equal (- x) c)|))
 (62 62 (:REWRITE |(equal (- x) (- y))|))
 (60 60 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (60 60 (:REWRITE RTL::BITS-NEG-INDICES))
 (59
  59
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (40 10 (:REWRITE RATIONALP-X))
 (16 16 (:TYPE-PRESCRIPTION BOOLEANP))
 (10 10 (:REWRITE REDUCE-RATIONALP-+))
 (10 10 (:REWRITE REDUCE-RATIONALP-*))
 (10 10 (:REWRITE RATIONALP-MINUS-X))
 (10 10 (:META META-RATIONALP-CORRECT))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::INT-RP-1
 (1684 574 (:REWRITE DEFAULT-TIMES-2))
 (683 574 (:REWRITE DEFAULT-TIMES-1))
 (265 265
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (121 121
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (121 121
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (121 121
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (79 79 (:REWRITE REDUCE-INTEGERP-+))
 (79 79 (:REWRITE INTEGERP-MINUS-X))
 (79 79 (:META META-INTEGERP-CORRECT))
 (72 24 (:REWRITE SIMPLIFY-SUMS-<))
 (72 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (72 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (54 54 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (54 54 (:REWRITE RTL::BITS-NEG-INDICES))
 (51 27
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (51 27 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (48 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (48 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (43 43 (:REWRITE SUBSETP-MEMBER . 4))
 (43 43 (:REWRITE SUBSETP-MEMBER . 3))
 (43 43 (:REWRITE SUBSETP-MEMBER . 2))
 (43 43 (:REWRITE SUBSETP-MEMBER . 1))
 (43 43 (:REWRITE INTERSECTP-MEMBER . 3))
 (43 43 (:REWRITE INTERSECTP-MEMBER . 2))
 (39
  39
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (27 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (27 27
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (27 27
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (27 27 (:REWRITE |(equal c (/ x))|))
 (27 27 (:REWRITE |(equal c (- x))|))
 (27 27 (:REWRITE |(equal (/ x) c)|))
 (27 27 (:REWRITE |(equal (/ x) (/ y))|))
 (27 27 (:REWRITE |(equal (- x) c)|))
 (27 27 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (24 24
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (24 24 (:REWRITE INTEGERP-<-CONSTANT))
 (24 24 (:REWRITE CONSTANT-<-INTEGERP))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< c (- x))|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< (/ x) (/ y))|))
 (24 24 (:REWRITE |(< (- x) c)|))
 (24 24 (:REWRITE |(< (- x) (- y))|))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (8 2 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::BITS-RP-1-0
 (195 27 (:REWRITE ACL2-NUMBERP-X))
 (156 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (144 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (96 4 (:REWRITE MOD-ZERO . 4))
 (84 21 (:REWRITE RATIONALP-X))
 (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (44 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (44 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (35 5 (:REWRITE DEFAULT-MOD-RATIO))
 (34 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 32
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (28 14 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (26 26 (:REWRITE REDUCE-INTEGERP-+))
 (26 26 (:REWRITE INTEGERP-MINUS-X))
 (26 26 (:META META-INTEGERP-CORRECT))
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (21 21 (:REWRITE REDUCE-RATIONALP-+))
 (21 21 (:REWRITE REDUCE-RATIONALP-*))
 (21 21 (:REWRITE RATIONALP-MINUS-X))
 (21 21 (:META META-RATIONALP-CORRECT))
 (18 18
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (15 15
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (15 15
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (15 15
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (15 15
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (14 14
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (14 14 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (14 14 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (14 14 (:TYPE-PRESCRIPTION NATP))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (14 14
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (13 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (12 4 (:REWRITE RTL::BITS-TAIL))
 (11 11 (:REWRITE DEFAULT-MOD-2))
 (10 10 (:REWRITE DEFAULT-PLUS-2))
 (10 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (5 5 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RTL::BITS-RN-1-0
 (195 27 (:REWRITE ACL2-NUMBERP-X))
 (156 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (144 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (96 4 (:REWRITE MOD-ZERO . 4))
 (84 21 (:REWRITE RATIONALP-X))
 (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (44 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (44 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (35 5 (:REWRITE DEFAULT-MOD-RATIO))
 (34 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 32
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (28 14 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (26 26 (:REWRITE REDUCE-INTEGERP-+))
 (26 26 (:REWRITE INTEGERP-MINUS-X))
 (26 26 (:META META-INTEGERP-CORRECT))
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (21 21 (:REWRITE REDUCE-RATIONALP-+))
 (21 21 (:REWRITE REDUCE-RATIONALP-*))
 (21 21 (:REWRITE RATIONALP-MINUS-X))
 (21 21 (:META META-RATIONALP-CORRECT))
 (18 18
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (15 15
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (15 15
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (15 15
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (15 15
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (14 14
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (14 14 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (14 14 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (14 14 (:TYPE-PRESCRIPTION NATP))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (14 14
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (13 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (12 4 (:REWRITE RTL::BITS-TAIL))
 (11 11 (:REWRITE DEFAULT-MOD-2))
 (10 10 (:REWRITE DEFAULT-PLUS-2))
 (10 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (5 5 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RTL::INTEGERP-EXPDIFF
 (58 32 (:REWRITE DEFAULT-PLUS-1))
 (55 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:META META-RATIONALP-CORRECT))
 (2 1
    (:TYPE-PRESCRIPTION RTL::INTEGERP-EXPDIFF))
 (2 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::EXPQ-EXPDIFF
 (3110 68 (:REWRITE RTL::NEG-BITN-0))
 (2741 68 (:REWRITE RTL::NEG-BITN-1))
 (580 266 (:REWRITE DEFAULT-LESS-THAN-1))
 (415 305 (:REWRITE DEFAULT-PLUS-1))
 (415 208
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (412 305 (:REWRITE DEFAULT-PLUS-2))
 (410 208
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (308 9 (:REWRITE |(+ (if a b c) x)|))
 (307 266 (:REWRITE DEFAULT-LESS-THAN-2))
 (266 266 (:REWRITE THE-FLOOR-BELOW))
 (266 266 (:REWRITE THE-FLOOR-ABOVE))
 (261 49
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (260 208 (:REWRITE SIMPLIFY-SUMS-<))
 (246 246
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (246 246
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (211 209
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (211 209
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (209 209 (:REWRITE INTEGERP-<-CONSTANT))
 (209 209 (:REWRITE CONSTANT-<-INTEGERP))
 (209 209
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (209 209
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (209 209
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (209 209 (:REWRITE |(< c (- x))|))
 (209 209
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (209 209
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (209 209
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (209 209 (:REWRITE |(< (/ x) (/ y))|))
 (209 209 (:REWRITE |(< (- x) c)|))
 (209 209 (:REWRITE |(< (- x) (- y))|))
 (206 68 (:REWRITE RTL::BVECP-BITN-0))
 (200 47 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (156 156
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (118
   118
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (118
  118
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (118 118
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (118
     118
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (118 118
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (118 118
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (88 67 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (81 81 (:REWRITE |(< (* x y) 0)|))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (75 75 (:REWRITE |(< (/ x) 0)|))
 (68 68 (:REWRITE RTL::BITN-NEG))
 (62 62 (:REWRITE |(< (+ c/d x) y)|))
 (49 49
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (49 49
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (49 49
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (49 49 (:REWRITE |(equal c (/ x))|))
 (49 49 (:REWRITE |(equal c (- x))|))
 (49 49 (:REWRITE |(equal (/ x) c)|))
 (49 49 (:REWRITE |(equal (/ x) (/ y))|))
 (49 49 (:REWRITE |(equal (- x) c)|))
 (49 49 (:REWRITE |(equal (- x) (- y))|))
 (21 21 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (21 21 (:REWRITE RTL::BITS-NEG-INDICES))
 (15 5 (:REWRITE RTL::BITS-TAIL))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (1 1 (:REWRITE RTL::BITS-BVECP)))
(RTL::INTEGERP-EXPQ
 (66 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (39 1 (:REWRITE |(< (+ (- c) x) y)|))
 (26 13 (:TYPE-PRESCRIPTION RTL::INT-SI))
 (8 3 (:REWRITE DEFAULT-LESS-THAN-1))
 (7 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 3 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 2 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE THE-FLOOR-BELOW))
 (3 3 (:REWRITE THE-FLOOR-ABOVE))
 (3 3
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3 1 (:REWRITE DEFAULT-PLUS-2))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 1
    (:TYPE-PRESCRIPTION RTL::INTEGERP-EXPQ))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE DEFAULT-PLUS-1))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(RTL::QUOTIENT-EXPQ
 (48287 7109 (:REWRITE DEFAULT-TIMES-2))
 (31062 7109 (:REWRITE DEFAULT-TIMES-1))
 (12562 12562
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12562 12562
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12562 12562
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (11382 271 (:REWRITE RTL::NEG-BITN-0))
 (11288 8268
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (11288 8268
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (11288 8268
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (10026 271 (:REWRITE RTL::NEG-BITN-1))
 (8803
  8803
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8803
      8803
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8803
     8803
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8803 8803
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8803 8803
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7557 1517
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
 (7557 1517
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
 (7557 1517
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
 (6758 6758
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (6758 6758
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6758 6758
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6270 346
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5977 346 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3768 2240 (:REWRITE DEFAULT-PLUS-1))
 (3766 2240 (:REWRITE DEFAULT-PLUS-2))
 (2009 983
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1999 983
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1944 1024 (:REWRITE DEFAULT-LESS-THAN-1))
 (1832 509 (:REWRITE DEFAULT-EXPT-2))
 (1741 1729
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (1741 1729
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (1741 1729
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (1431 983 (:REWRITE SIMPLIFY-SUMS-<))
 (1264 1024 (:REWRITE DEFAULT-LESS-THAN-2))
 (1225 983
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1225 983
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1158 772
       (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (1066 983 (:REWRITE |(< (/ x) (/ y))|))
 (1024 1024 (:REWRITE THE-FLOOR-BELOW))
 (1024 1024 (:REWRITE THE-FLOOR-ABOVE))
 (998 998
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (998 998 (:REWRITE NORMALIZE-ADDENDS))
 (983 983
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (983 983 (:REWRITE INTEGERP-<-CONSTANT))
 (983 983 (:REWRITE CONSTANT-<-INTEGERP))
 (983 983
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (983 983
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (983 983
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (983 983
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (983 983 (:REWRITE |(< c (- x))|))
 (983 983
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (983 983
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (983 983
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (983 983
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (983 983 (:REWRITE |(< (- x) c)|))
 (983 983 (:REWRITE |(< (- x) (- y))|))
 (813 271 (:REWRITE RTL::BVECP-BITN-0))
 (786 262 (:TYPE-PRESCRIPTION RTL::SI))
 (784 346
      (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4F))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3P))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3F))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2P))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2F))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1P))
 (755 755
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1F))
 (570 310 (:REWRITE DEFAULT-DIVIDE))
 (557 117 (:REWRITE DEFAULT-MINUS))
 (509 509 (:REWRITE DEFAULT-EXPT-1))
 (489 406 (:REWRITE |(< (/ x) 0)|))
 (441 441 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (418 346 (:REWRITE |(equal (- x) (- y))|))
 (406 406
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (406 406
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (406 406 (:REWRITE |(< (* x y) 0)|))
 (402 402
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (402 402 (:REWRITE RTL::BITS-NEG-INDICES))
 (386 386 (:REWRITE |(expt 1/c n)|))
 (386 386 (:REWRITE |(expt (- x) n)|))
 (386 346 (:REWRITE |(equal (/ x) (/ y))|))
 (346 346
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (346 346
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (346 346
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (346 346 (:REWRITE |(equal c (/ x))|))
 (346 346 (:REWRITE |(equal c (- x))|))
 (346 346 (:REWRITE |(equal (/ x) c)|))
 (346 346 (:REWRITE |(equal (- x) c)|))
 (336 336 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (307 307
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (271 271 (:REWRITE RTL::BITN-NEG))
 (224 224 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (121 121 (:REWRITE SUBSETP-MEMBER . 4))
 (121 121 (:REWRITE SUBSETP-MEMBER . 3))
 (121 121 (:REWRITE SUBSETP-MEMBER . 2))
 (121 121 (:REWRITE SUBSETP-MEMBER . 1))
 (121 121 (:REWRITE INTERSECTP-MEMBER . 3))
 (121 121 (:REWRITE INTERSECTP-MEMBER . 2))
 (117 13 (:REWRITE ACL2-NUMBERP-X))
 (84 84
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (82 82
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (82 82
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (82 82 (:REWRITE |(< 0 (/ x))|))
 (82 82 (:REWRITE |(< 0 (* x y))|))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (56 56 (:REWRITE |(* (- x) y)|))
 (52 13 (:REWRITE RATIONALP-X))
 (26 26 (:TYPE-PRESCRIPTION BOOLEANP))
 (13 13 (:REWRITE REDUCE-RATIONALP-+))
 (13 13 (:REWRITE REDUCE-RATIONALP-*))
 (13 13 (:REWRITE REDUCE-INTEGERP-+))
 (13 13 (:REWRITE RATIONALP-MINUS-X))
 (13 13 (:REWRITE INTEGERP-MINUS-X))
 (13 13 (:META META-RATIONALP-CORRECT))
 (13 13 (:META META-INTEGERP-CORRECT))
 (9 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
 (8 8
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G)))
