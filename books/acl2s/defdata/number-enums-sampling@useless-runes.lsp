(ACL2S::NTH-NAT-BUILTIN (1 1
                           (:TYPE-PRESCRIPTION ACL2S::NTH-NAT-BUILTIN)))
(ACL2S::NAT-INDEX (1 1
                     (:TYPE-PRESCRIPTION ACL2S::NAT-INDEX)))
(ACL2S::NTH-POS-BUILTIN)
(ACL2S::NTH-POS-BUILTIN-GUARD-IMPLIES-TEST)
(ACL2S::NTH-POS-BUILTIN)
(ACL2S::NTH-POS-BUILTIN-IS-POSP (1 1 (:REWRITE DEFAULT-<-2))
                                (1 1 (:REWRITE DEFAULT-<-1))
                                (1 1 (:REWRITE DEFAULT-+-2))
                                (1 1 (:REWRITE DEFAULT-+-1)))
(ACL2S::POS-INDEX)
(ACL2S::POS-INDEX-GUARD-IMPLIES-TEST)
(ACL2S::POS-INDEX)
(ACL2S::NEGP)
(ACL2S::NTH-NEG-BUILTIN)
(ACL2S::NON-POS-INTEGERP)
(ACL2S::NTH-NON-POS-INTEGER-BUILTIN)
(ACL2S::NON-0-INTEGERP)
(ACL2S::NTH-NON-0-INTEGER-BUILTIN)
(ACL2S::NTH-INTEGER-BUILTIN)
(ACL2S::SIMPLE-HASH)
(ACL2S::NTH-INTEGER-BETWEEN (20 10 (:REWRITE DEFAULT-+-2))
                            (18 13 (:REWRITE DEFAULT-*-1))
                            (16 13 (:REWRITE DEFAULT-*-2))
                            (16 1
                                (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                            (14 10 (:REWRITE DEFAULT-+-1))
                            (8 5 (:REWRITE DEFAULT-UNARY-MINUS))
                            (6 6 (:REWRITE DEFAULT-<-2))
                            (6 6 (:REWRITE DEFAULT-<-1))
                            (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                            (3 1 (:REWRITE COMMUTATIVITY-OF-+))
                            (3 1 (:DEFINITION NFIX))
                            (1 1 (:REWRITE DEFAULT-UNARY-/))
                            (1 1 (:REWRITE DEFAULT-NUMERATOR))
                            (1 1 (:REWRITE DEFAULT-DENOMINATOR))
                            (1 1 (:DEFINITION IFIX)))
(ACL2S::BITSIZE-AUX
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (81 31 (:REWRITE DEFAULT-PLUS-2))
     (79 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (75 31 (:REWRITE DEFAULT-PLUS-1))
     (67 67 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (65 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (45 5
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (45 5
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (45 5
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (31 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (23 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (23 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (23 18 (:REWRITE |(< (- x) (- y))|))
     (22 22 (:REWRITE DEFAULT-TIMES-2))
     (22 22 (:REWRITE DEFAULT-TIMES-1))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 6 (:REWRITE DEFAULT-MINUS))
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
     (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (17 17
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (17 17 (:REWRITE INTEGERP-<-CONSTANT))
     (17 17 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:REWRITE |(* (- x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE |(< (/ x) y) with (< x 0)|)))
(ACL2S::BITSIZE-AUX-POSP
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (104 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (66 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (48 46 (:REWRITE DEFAULT-LESS-THAN-2))
     (46 46 (:REWRITE THE-FLOOR-BELOW))
     (46 46 (:REWRITE THE-FLOOR-ABOVE))
     (46 46 (:REWRITE DEFAULT-LESS-THAN-1))
     (46 45
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (46 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (45 45 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (45 45
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (45 45 (:REWRITE INTEGERP-<-CONSTANT))
     (45 45 (:REWRITE CONSTANT-<-INTEGERP))
     (45 45
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (45 45
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (45 45
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (45 45
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (45 45 (:REWRITE |(< c (- x))|))
     (45 45
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (45 45
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (45 45
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (45 45
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (45 45 (:REWRITE |(< (/ x) (/ y))|))
     (45 45 (:REWRITE |(< (- x) c)|))
     (45 45 (:REWRITE |(< (- x) (- y))|))
     (42 40
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (42 40 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (40 40 (:REWRITE SIMPLIFY-SUMS-<))
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
     (36 36 (:REWRITE DEFAULT-TIMES-2))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
     (33 33 (:REWRITE REDUCE-INTEGERP-+))
     (33 33 (:REWRITE INTEGERP-MINUS-X))
     (33 33 (:META META-INTEGERP-CORRECT))
     (28 28
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 6 (:REWRITE |(* y x)|))
     (17 17 (:REWRITE |(< (/ x) 0)|))
     (17 17 (:REWRITE |(< (* x y) 0)|))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (16 16 (:REWRITE DEFAULT-PLUS-2))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(ACL2S::BITSIZE)
(ACL2S::ROUNDS)
(ACL2S::NTH-INTEGER-BETWEEN-BITS-MID
 (1044 1044
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1044 1044
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1044 1044
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (672 279 (:REWRITE DEFAULT-PLUS-2))
 (632
   632
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (632
  632
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (632 632
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (632
     632
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (632 632
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (632 632
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (564 36 (:REWRITE INTEGERP-MINUS-X))
 (538 279 (:REWRITE DEFAULT-PLUS-1))
 (500 2 (:REWRITE CANCEL-MOD-+))
 (471 55
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (384 30 (:META META-INTEGERP-CORRECT))
 (376 18
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (350 4 (:REWRITE INTEGERP-/))
 (328 8 (:REWRITE DEFAULT-FLOOR-RATIO))
 (242 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (242 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (220 188 (:REWRITE DEFAULT-TIMES-2))
 (220 52 (:REWRITE DEFAULT-MINUS))
 (188 188 (:REWRITE DEFAULT-TIMES-1))
 (184 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (182 30 (:REWRITE REDUCE-INTEGERP-+))
 (180 2 (:REWRITE MOD-X-Y-=-X . 3))
 (167 8 (:REWRITE |(floor (+ x r) i)|))
 (162 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (160 2 (:REWRITE MOD-X-Y-=-X . 2))
 (142 142
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (138 45 (:REWRITE |(< (- x) c)|))
 (109 55 (:REWRITE DEFAULT-LESS-THAN-2))
 (103 103
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (88 2 (:REWRITE MOD-ZERO . 3))
 (85 77 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (85 77 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (85 77
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (85 77
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (77 77 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (77 77
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (77 77 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (77 77
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (77 77 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (76 40
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (76 2 (:REWRITE MOD-X-Y-=-X . 4))
 (74 6 (:REWRITE |(* (* x y) z)|))
 (57 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (57 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 29 (:REWRITE SIMPLIFY-SUMS-<))
 (55 55 (:REWRITE THE-FLOOR-BELOW))
 (55 55 (:REWRITE THE-FLOOR-ABOVE))
 (55 55 (:REWRITE DEFAULT-LESS-THAN-1))
 (52 2 (:LINEAR EXPT-X->=-X))
 (52 2 (:LINEAR EXPT-X->-X))
 (50 18 (:REWRITE |(equal (+ (- c) x) y)|))
 (50 2 (:REWRITE DEFAULT-MOD-RATIO))
 (45 45
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (45 45
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (45 45
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (45 45
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (45 45 (:REWRITE |(< c (- x))|))
 (45 45
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (45 45
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (45 45
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (45 45
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (45 45 (:REWRITE |(< (/ x) (/ y))|))
 (45 45 (:REWRITE |(< (- x) (- y))|))
 (43 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 42
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (42 42 (:REWRITE INTEGERP-<-CONSTANT))
 (42 42 (:REWRITE CONSTANT-<-INTEGERP))
 (40 2 (:REWRITE MOD-ZERO . 4))
 (34 34 (:REWRITE |(* (- x) y)|))
 (24 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:REWRITE |(< (+ c/d x) y)|))
 (18 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (18 18
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (18 18 (:REWRITE |(equal c (/ x))|))
 (18 18 (:REWRITE |(equal c (- x))|))
 (18 18 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(equal (/ x) (/ y))|))
 (18 18 (:REWRITE |(equal (- x) c)|))
 (18 18 (:REWRITE |(equal (- x) (- y))|))
 (18 18 (:REWRITE |(< x (+ c/d y))|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (10 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (10 2 (:REWRITE MOD-CANCEL-*-CONST))
 (10 2
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (10 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (10 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (10 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE DEFAULT-FLOOR-2))
 (8 8 (:REWRITE DEFAULT-FLOOR-1))
 (8 8 (:REWRITE |(floor x 2)| . 2))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(* c (* d x))|))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(- (- x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE DEFAULT-MOD-1))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(ACL2S::NTH-INTEGER-BETWEEN-BITS-LO
 (459 2 (:REWRITE CANCEL-MOD-+))
 (357 3 (:REWRITE DEFAULT-MOD-RATIO))
 (327 11 (:REWRITE INTEGERP-MINUS-X))
 (299 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (287 2 (:REWRITE MOD-X-Y-=-X . 3))
 (261
   261
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (261
  261
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (261 261
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (261
     261
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (261 261
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (261 261
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (232 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (222 29 (:REWRITE DEFAULT-TIMES-2))
 (204 9 (:META META-INTEGERP-CORRECT))
 (200 101 (:REWRITE DEFAULT-PLUS-2))
 (198 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (189 10
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (175 2 (:REWRITE INTEGERP-/))
 (172 2 (:REWRITE MOD-ZERO . 3))
 (170 8 (:REWRITE |(* (* x y) z)|))
 (146 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (146 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (111 101 (:REWRITE DEFAULT-PLUS-1))
 (105 2 (:REWRITE MOD-X-Y-=-X . 2))
 (87 2 (:REWRITE MOD-X-Y-=-X . 4))
 (83 1 (:REWRITE |(* x (if a b c))|))
 (82 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (81 9 (:REWRITE DEFAULT-DIVIDE))
 (70 25 (:REWRITE DEFAULT-LESS-THAN-1))
 (70 8 (:REWRITE |(< y (+ (- c) x))|))
 (64 19
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (61 25 (:REWRITE DEFAULT-LESS-THAN-2))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (51 2 (:REWRITE MOD-ZERO . 4))
 (48 3 (:REWRITE DEFAULT-MOD-2))
 (46 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (46 1 (:REWRITE |(/ (if a b c))|))
 (40 13 (:REWRITE SIMPLIFY-SUMS-<))
 (39 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (39 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (37 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (37 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (37 27
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (37 27
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (32 7 (:REWRITE DEFAULT-MINUS))
 (30 4
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (30 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (29 29 (:REWRITE DEFAULT-TIMES-1))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (28 2 (:LINEAR EXPT->-1-ONE))
 (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (27 27
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (27 27
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (27 2 (:REWRITE |(- (* c x))|))
 (26 26 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (26 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25 (:REWRITE THE-FLOOR-BELOW))
 (25 25 (:REWRITE THE-FLOOR-ABOVE))
 (25 9 (:REWRITE |(equal (+ (- c) x) y)|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 4 (:REWRITE |(/ (expt x n))|))
 (21 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (21 2 (:REWRITE MOD-CANCEL-*-CONST))
 (21 2
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (21 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (20 20
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (20 20
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (14 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (10 10 (:REWRITE |(* c (* d x))|))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE DEFAULT-MOD-1))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(ACL2S::INTEGER-INDEX)
(ACL2S::NEG-RATIOP)
(ACL2S::BASE-DEFDATA-INSERT
     (2 2 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE DEFAULT-CDR))
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
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::BASE-DEFDATA-ISORT
     (2034 175 (:REWRITE DEFAULT-LESS-THAN-2))
     (882 98 (:REWRITE ACL2-NUMBERP-X))
     (392 98 (:REWRITE RATIONALP-X))
     (175 175 (:REWRITE THE-FLOOR-BELOW))
     (175 175 (:REWRITE THE-FLOOR-ABOVE))
     (163 163 (:REWRITE REDUCE-INTEGERP-+))
     (163 163 (:REWRITE INTEGERP-MINUS-X))
     (163 163 (:META META-INTEGERP-CORRECT))
     (128 119 (:REWRITE DEFAULT-CAR))
     (126 126 (:REWRITE SIMPLIFY-SUMS-<))
     (126 126
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (126 126 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (126 126
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (126 126
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (126 126
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (126 126
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (126 126
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (126 126 (:REWRITE INTEGERP-<-CONSTANT))
     (126 126 (:REWRITE CONSTANT-<-INTEGERP))
     (126 126
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (126 126
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (126 126
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (126 126
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (126 126 (:REWRITE |(< c (- x))|))
     (126 126
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (126 126
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (126 126
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (126 126
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (126 126 (:REWRITE |(< (/ x) (/ y))|))
     (126 126 (:REWRITE |(< (- x) c)|))
     (126 126 (:REWRITE |(< (- x) (- y))|))
     (98 98 (:REWRITE REDUCE-RATIONALP-+))
     (98 98 (:REWRITE REDUCE-RATIONALP-*))
     (98 98 (:REWRITE RATIONALP-MINUS-X))
     (98 98 (:META META-RATIONALP-CORRECT))
     (90 81 (:REWRITE DEFAULT-CDR))
     (78 78
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (78 78
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (78 78 (:REWRITE |(< (/ x) 0)|))
     (78 78 (:REWRITE |(< (* x y) 0)|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (23 23 (:REWRITE |(< 0 (/ x))|))
     (23 23 (:REWRITE |(< 0 (* x y))|)))
(ACL2S::POS-RATIOP)
(ACL2S::NTH-POS-RATIO-BUILTIN (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(ACL2S::NTH-NEG-RATIO-BUILTIN)
(ACL2S::NEG-RATIONALP)
(ACL2S::NTH-NEG-RATIONAL-BUILTIN
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::POS-RATIONALP)
(ACL2S::NTH-POS-RATIONAL-BUILTIN
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NON-NEG-RATIONALP)
(ACL2S::NTH-NON-NEG-RATIONAL-BUILTIN
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NON-POS-RATIONALP)
(ACL2S::NTH-NON-POS-RATIONAL-BUILTIN
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NON-0-RATIONALP)
(ACL2S::NTH-NON-0-RATIONAL-BUILTIN
     (13 8 (:REWRITE DEFAULT-TIMES-2))
     (12 5 (:REWRITE DEFAULT-PLUS-2))
     (11 8 (:REWRITE DEFAULT-TIMES-1))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-RATIONAL-BUILTIN
     (30 18 (:REWRITE DEFAULT-TIMES-2))
     (24 18 (:REWRITE DEFAULT-TIMES-1))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (21 5 (:REWRITE DEFAULT-PLUS-2))
     (18 2 (:REWRITE DEFAULT-MOD-RATIO))
     (14 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-RAT-IS-RATP
     (73 31 (:REWRITE DEFAULT-TIMES-2))
     (58 31 (:REWRITE DEFAULT-TIMES-1))
     (56 6 (:REWRITE DEFAULT-PLUS-2))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 2 (:REWRITE DEFAULT-MOD-RATIO))
     (15 15
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (15 6 (:REWRITE DEFAULT-PLUS-1))
     (14 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (9 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (4 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (4 2
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(* (- x) y)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 2 (:REWRITE |(* c (* d x))|))
     (2 1 (:REWRITE DEFAULT-FLOOR-1))
     (2 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(* x (- y))|)))
(ACL2S::NTH-RATIONAL-BETWEEN
     (254 30 (:REWRITE DEFAULT-TIMES-1))
     (244 30 (:REWRITE DEFAULT-TIMES-2))
     (198 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (191 1 (:REWRITE CANCEL-MOD-+))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (147 7 (:REWRITE INTEGERP-MINUS-X))
     (124 14
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (113 23 (:REWRITE DEFAULT-PLUS-2))
     (105 21 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (105 21 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (105 21
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (105 21
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (98 6 (:META META-INTEGERP-CORRECT))
     (85 2 (:REWRITE INTEGERP-/))
     (82 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (82 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (69 1 (:REWRITE MOD-X-Y-=-X . 2))
     (68 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (68 1 (:REWRITE MOD-X-Y-=-X . 3))
     (67 23 (:REWRITE DEFAULT-PLUS-1))
     (61 1 (:REWRITE MOD-ZERO . 3))
     (58 5 (:REWRITE DEFAULT-MINUS))
     (55 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (53 1 (:REWRITE MOD-X-Y-=-X . 4))
     (52 7
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (49 16
         (:LINEAR DEFDATA::NTH-WEIGHTED-SPLIT-NAT--BOUND))
     (45 3 (:REWRITE |(+ y (+ x z))|))
     (37 1 (:REWRITE MOD-ZERO . 4))
     (34 1 (:REWRITE DEFAULT-MOD-RATIO))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (25 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (23 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (21 21
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (21 21 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (21 21 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (21 21
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (21 21 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (17 17
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (17 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (16 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (16 12 (:REWRITE SIMPLIFY-SUMS-<))
     (15 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 1
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (13 3 (:REWRITE |(- (* c x))|))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (10 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (9 6 (:REWRITE DEFAULT-DIVIDE))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (8 2 (:REWRITE RATIONALP-X))
     (7 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (7 1 (:REWRITE MOD-CANCEL-*-CONST))
     (7 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (7 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(* c (* d x))|))
     (5 5 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 1 (:REWRITE DEFAULT-MOD-2))
     (2 1 (:REWRITE DEFAULT-MOD-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(equal (* x y) 0)|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-COMPLEX-RATIONAL-BUILTIN
     (60 60
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (25 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 13 (:REWRITE DEFAULT-LESS-THAN-1))
     (22 6 (:REWRITE DEFAULT-PLUS-2))
     (18 9
         (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (13 13 (:REWRITE THE-FLOOR-BELOW))
     (13 13 (:REWRITE THE-FLOOR-ABOVE))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (13 13 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (13 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (13 13
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (13 13
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (13 13
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
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
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (12 6 (:REWRITE DEFAULT-TIMES-2))
     (10 6 (:REWRITE DEFAULT-TIMES-1))
     (8 6 (:REWRITE DEFAULT-PLUS-1))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-COMPLEX-RATIONAL-BETWEEN
     (460 2 (:REWRITE CANCEL-MOD-+))
     (454 56 (:REWRITE DEFAULT-TIMES-1))
     (444 56 (:REWRITE DEFAULT-TIMES-2))
     (394 48 (:REWRITE DEFAULT-PLUS-2))
     (367 9 (:REWRITE INTEGERP-MINUS-X))
     (320 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (269 7 (:META META-INTEGERP-CORRECT))
     (248 4 (:REWRITE INTEGERP-/))
     (245 25
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (224 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (224 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (224 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (192 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (190 38
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (190 38
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (164 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (164 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (156 36
          (:LINEAR DEFDATA::NTH-WEIGHTED-SPLIT-NAT--BOUND))
     (142 48 (:REWRITE DEFAULT-PLUS-1))
     (138 2 (:REWRITE MOD-X-Y-=-X . 2))
     (136 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (122 2 (:REWRITE MOD-ZERO . 3))
     (122 2 (:REWRITE MOD-X-Y-=-X . 3))
     (118 8 (:REWRITE DEFAULT-MINUS))
     (112 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (106 2 (:REWRITE MOD-X-Y-=-X . 4))
     (102 12
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (90 6 (:REWRITE |(+ y (+ x z))|))
     (74 2 (:REWRITE MOD-ZERO . 4))
     (68 2 (:REWRITE DEFAULT-MOD-RATIO))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (48 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (46 46
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (43 25 (:REWRITE DEFAULT-LESS-THAN-1))
     (39 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (38 38
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (38 38 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (38 38 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (38 38
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (38 38 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (32 32
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (31 25 (:REWRITE DEFAULT-LESS-THAN-2))
     (30 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (30 2
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (29 25
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (29 25
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 19 (:REWRITE SIMPLIFY-SUMS-<))
     (26 6 (:REWRITE |(- (* c x))|))
     (25 25 (:REWRITE THE-FLOOR-BELOW))
     (25 25 (:REWRITE THE-FLOOR-ABOVE))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (18 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (16 8 (:REWRITE DEFAULT-DIVIDE))
     (14 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 2
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 2 (:REWRITE MOD-CANCEL-*-CONST))
     (14 2
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (14 2
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (12 12 (:REWRITE |(* c (* d x))|))
     (12 6
         (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:TYPE-PRESCRIPTION ABS))
     (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE DEFAULT-REALPART))
     (4 4 (:REWRITE DEFAULT-IMAGPART))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 2 (:REWRITE DEFAULT-MOD-2))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(mod x (- y))| . 3))
     (2 2 (:REWRITE |(mod x (- y))| . 2))
     (2 2 (:REWRITE |(mod x (- y))| . 1))
     (2 2
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(mod (- x) y)| . 3))
     (2 2 (:REWRITE |(mod (- x) y)| . 2))
     (2 2 (:REWRITE |(mod (- x) y)| . 1))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(equal (* x y) 0)|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-ACL2-NUMBER-BUILTIN
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 5
         (:TYPE-PRESCRIPTION ACL2S::NTH-RAT-IS-RATP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 2 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE DEFDATA::MY-MV-NTH--REDUCE1))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-ACL2-NUMBER-BETWEEN)
(ACL2S::NTH-NUMBER-BETWEEN-FN)
(DEFDATA::GEOMETRIC-INT-AROUND)
(DEFDATA::GEOMETRIC-RAT-AROUND
     (8 4
        (:TYPE-PRESCRIPTION ACL2S::NTH-RAT-IS-RATP))
     (4 4 (:TYPE-PRESCRIPTION NATP)))
(DEFDATA::GEOMETRIC-INT-LEQ (5 5
                               (:TYPE-PRESCRIPTION ACL2S::NTH-NAT-BUILTIN)))
(DEFDATA::GEOMETRIC-RAT-LEQ)
(DEFDATA::GEOMETRIC-INT-GEQ (4 4
                               (:TYPE-PRESCRIPTION ACL2S::NTH-NAT-BUILTIN)))
(DEFDATA::GEOMETRIC-RAT-GEQ)
(DEFDATA::GEOMETRIC-INT-AROUND-BND)
(DEFDATA::GEOMETRIC-RAT-AROUND-BND
     (10 5
         (:TYPE-PRESCRIPTION ACL2S::NTH-RAT-IS-RATP))
     (5 5 (:TYPE-PRESCRIPTION NATP)))
(DEFDATA::GEOMETRIC-INT-LEQ-BND
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::NTH-NAT-BUILTIN)))
(DEFDATA::GEOMETRIC-RAT-LEQ-BND)
(DEFDATA::GEOMETRIC-INT-GEQ-BND
     (5 5
        (:TYPE-PRESCRIPTION ACL2S::NTH-NAT-BUILTIN)))
(DEFDATA::GEOMETRIC-RAT-GEQ-BND)
(DEFDATA::GEOMETRIC-INT-BETWEEN
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
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
(DEFDATA::GEOMETRIC-RAT-BETWEEN
     (12 6
         (:TYPE-PRESCRIPTION ACL2S::NTH-RAT-IS-RATP))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (6 6 (:TYPE-PRESCRIPTION NATP)))
