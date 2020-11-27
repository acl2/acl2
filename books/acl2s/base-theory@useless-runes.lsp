(ACL2S::ACL2S-DEFAULT-MOD-RATIO
     (799 799
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (799 799
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (799 799
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (577 67 (:REWRITE RATIONALP-X))
     (540 108 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (448 108 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (304 8 (:LINEAR MOD-BOUNDS-2))
     (304 8 (:LINEAR MOD-BOUNDS-1))
     (154 154 (:REWRITE DEFAULT-TIMES-2))
     (154 154 (:REWRITE DEFAULT-TIMES-1))
     (147 4 (:REWRITE MOD-X-Y-=-X . 4))
     (146 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (146 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (131 4
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (130 4 (:REWRITE MOD-ZERO . 4))
     (120 108
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (120 108
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (110 10
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (108 108 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (108 108 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (108 108
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (108 108
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (108 108
          (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (108 108
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (108 108
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (108 108 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (108 108 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (108 108
          (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (93 13 (:REWRITE ACL2-NUMBERP-X))
     (87 87
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (86 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (84 4 (:REWRITE MOD-ZERO . 3))
     (84 4 (:LINEAR MOD-BOUNDS-3))
     (74 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (74 4 (:REWRITE MOD-CANCEL-*-CONST))
     (74 4
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (74 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (68 68
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (68 68 (:REWRITE DEFAULT-DIVIDE))
     (67 67 (:REWRITE REDUCE-RATIONALP-+))
     (67 67 (:REWRITE REDUCE-RATIONALP-*))
     (67 67 (:REWRITE RATIONALP-MINUS-X))
     (67 67 (:META META-RATIONALP-CORRECT))
     (64 40 (:REWRITE DEFAULT-PLUS-2))
     (58 58 (:REWRITE INTEGERP-MINUS-X))
     (57 57 (:META META-INTEGERP-CORRECT))
     (47 40 (:REWRITE DEFAULT-PLUS-1))
     (46 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (46 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (46 2 (:REWRITE MOD-X-Y-=-X . 1))
     (36 4 (:REWRITE MOD-X-Y-=-X . 3))
     (35 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (35 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (19 4 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (9 9 (:REWRITE |(equal c (/ x))|))
     (9 9 (:REWRITE |(equal c (- x))|))
     (9 9 (:REWRITE |(equal (/ x) c)|))
     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
     (9 9 (:REWRITE |(equal (- x) c)|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (4 4 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(ACL2S::ACL2S-CANCEL-FLOOR-+)
(ACL2S::ACL2S-CANCEL-MOD-+
     (1085 75 (:REWRITE |(* y x)|))
     (985 25 (:REWRITE |(* x (+ y z))|))
     (623 183 (:REWRITE DEFAULT-TIMES-2))
     (526 62 (:REWRITE ACL2-NUMBERP-X))
     (452 4 (:LINEAR MOD-BOUNDS-2))
     (452 4 (:LINEAR MOD-BOUNDS-1))
     (338 338
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (338 338
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (338 338
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (268 67 (:REWRITE RATIONALP-X))
     (225 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (225 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (225 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (225 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (200 10 (:REWRITE |(+ x (if a b c))|))
     (178 2 (:LINEAR MOD-BOUNDS-3))
     (176 5 (:REWRITE MOD-X-Y-=-X . 4))
     (176 5 (:REWRITE MOD-X-Y-=-X . 3))
     (150 20 (:REWRITE |(+ (if a b c) x)|))
     (131 131 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (131 131
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (131 131
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (131 131
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (131 131
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (122 122 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (122 122
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (122 122
          (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (122 122
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (122 122 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (122 122 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (122 122
          (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (114 7 (:REWRITE MOD-ZERO . 4))
     (83 83
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (71 71 (:REWRITE REDUCE-INTEGERP-+))
     (71 71 (:REWRITE INTEGERP-MINUS-X))
     (71 71 (:META META-INTEGERP-CORRECT))
     (67 67 (:REWRITE REDUCE-RATIONALP-+))
     (67 67 (:REWRITE REDUCE-RATIONALP-*))
     (67 67 (:REWRITE RATIONALP-MINUS-X))
     (67 67 (:META META-RATIONALP-CORRECT))
     (66 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (66 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (48 48 (:REWRITE THE-FLOOR-BELOW))
     (48 48 (:REWRITE THE-FLOOR-ABOVE))
     (48 48 (:REWRITE SIMPLIFY-SUMS-<))
     (48 48
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (48 48
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (48 48
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (48 48 (:REWRITE INTEGERP-<-CONSTANT))
     (48 48 (:REWRITE DEFAULT-LESS-THAN-2))
     (48 48 (:REWRITE DEFAULT-LESS-THAN-1))
     (48 48 (:REWRITE CONSTANT-<-INTEGERP))
     (48 48
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (48 48
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (48 48
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (48 48
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (48 48 (:REWRITE |(< c (- x))|))
     (48 48
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (48 48 (:REWRITE |(< (/ x) (/ y))|))
     (48 48 (:REWRITE |(< (- x) c)|))
     (48 48 (:REWRITE |(< (- x) (- y))|))
     (40 10 (:REWRITE |(+ y x)|))
     (35 35
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (35 35 (:REWRITE DEFAULT-DIVIDE))
     (34 5 (:REWRITE MOD-X-Y-=-X . 2))
     (34 5
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (34 5 (:REWRITE MOD-CANCEL-*-CONST))
     (34 5
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (34 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (34 5
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (34 5
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (29 1
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
     (29 1
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (26 26 (:REWRITE NORMALIZE-ADDENDS))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< 0 (/ x))|))
     (24 24 (:REWRITE |(< 0 (* x y))|))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (20 20 (:REWRITE |(+ 0 x)|))
     (18 18 (:REWRITE DEFAULT-MOD-2))
     (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (9 9
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
     (2 2 (:REWRITE O-INFP->NEQ-0))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1
     (165 21 (:REWRITE ACL2-NUMBERP-X))
     (72 18 (:REWRITE RATIONALP-X))
     (38 38 (:REWRITE THE-FLOOR-BELOW))
     (38 38 (:REWRITE THE-FLOOR-ABOVE))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (24 24 (:REWRITE |(< (/ x) (/ y))|))
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (23 23 (:REWRITE INTEGERP-<-CONSTANT))
     (23 23 (:REWRITE CONSTANT-<-INTEGERP))
     (23 23 (:REWRITE |(< (- x) c)|))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE REDUCE-INTEGERP-+))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18 (:META META-RATIONALP-CORRECT))
     (18 18 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<2
     (165 21 (:REWRITE ACL2-NUMBERP-X))
     (72 18 (:REWRITE RATIONALP-X))
     (38 38 (:REWRITE THE-FLOOR-BELOW))
     (38 38 (:REWRITE THE-FLOOR-ABOVE))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (23 23 (:REWRITE INTEGERP-<-CONSTANT))
     (23 23 (:REWRITE CONSTANT-<-INTEGERP))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE REDUCE-INTEGERP-+))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18 (:META META-RATIONALP-CORRECT))
     (18 18 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< 0 (/ x))|))
     (7 7 (:REWRITE |(< 0 (* x y))|))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< x (+ c/d y))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL
     (46 6 (:REWRITE ACL2-NUMBERP-X))
     (20 5 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE DEFAULT-PLUS-2))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
(ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<
     (27 3 (:REWRITE ACL2-NUMBERP-X))
     (14 12 (:REWRITE DEFAULT-PLUS-1))
     (12 12 (:REWRITE DEFAULT-PLUS-2))
     (12 3 (:REWRITE RATIONALP-X))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<2))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL
     (27 3 (:REWRITE ACL2-NUMBERP-X))
     (14 12 (:REWRITE DEFAULT-PLUS-1))
     (12 12 (:REWRITE DEFAULT-PLUS-2))
     (12 3 (:REWRITE RATIONALP-X))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE O-INFP->NEQ-0)))
(ACL2S::NUMERATOR-1-DECREASES
     (285 285 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (285 285
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (285 285
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (285 285
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (37 12 (:REWRITE DEFAULT-PLUS-2))
     (24 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (17 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (17 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (13 12 (:REWRITE DEFAULT-PLUS-1))
     (11 1 (:REWRITE SIMPLIFY-SUMS-<))
     (11 1
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE DEFAULT-TIMES-2))
     (7 7 (:REWRITE DEFAULT-TIMES-1))
     (6 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (3 3
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-MINUS))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
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
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(* (- x) y)|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(ACL2S::ACL2S-NAT-UNDEFINED-NATP)
(ACL2S::NAT-IND-CONTRACT)
(ACL2S::NAT-IND-CONTRACT-TP)
(ACL2S::NAT-IND-CONTRACT-GENRULE)
(ACL2S::NAT-IND)
(ACL2S::NAT-IND-INDUCTION-SCHEME)
(ACL2S::NAT-IND-DEFINITION-RULE)
(ACL2S::ACL2S-POS-UNDEFINED-POSP)
(ACL2S::POS-IND-CONTRACT)
(ACL2S::POS-IND-CONTRACT-TP)
(ACL2S::POS-IND-CONTRACT-GENRULE)
(ACL2S::POS-IND)
(ACL2S::POS-IND-INDUCTION-SCHEME)
(ACL2S::POS-IND-DEFINITION-RULE)
(ACL2S::INT-IND-CONTRACT)
(ACL2S::INT-IND-CONTRACT-TP)
(ACL2S::INT-IND-CONTRACT-GENRULE)
(ACL2S::INT-IND)
(ACL2S::INT-IND-INDUCTION-SCHEME)
(ACL2S::INT-IND-DEFINITION-RULE)
(ACL2S::NAT-INDUCTION-SCHEME)
(ACL2S::POS-INDUCTION-SCHEME)
(ACL2S::INT-INDUCTION-SCHEME)
(ACL2S::CANCEL-<-+-1
     (65 9 (:REWRITE ACL2-NUMBERP-X))
     (32 8 (:REWRITE RATIONALP-X))
     (13 13 (:REWRITE THE-FLOOR-BELOW))
     (13 13 (:REWRITE THE-FLOOR-ABOVE))
     (13 13
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<2))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(ACL2S::CANCEL-<-+-2
     (65 9 (:REWRITE ACL2-NUMBERP-X))
     (32 8 (:REWRITE RATIONALP-X))
     (13 13 (:REWRITE THE-FLOOR-BELOW))
     (13 13 (:REWRITE THE-FLOOR-ABOVE))
     (13 13
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
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
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(ACL2S::CANCEL-<-*-1
     (56 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (40 10 (:REWRITE RATIONALP-X))
     (22 16
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (16 16 (:REWRITE THE-FLOOR-BELOW))
     (16 16 (:REWRITE THE-FLOOR-ABOVE))
     (16 16 (:REWRITE SIMPLIFY-SUMS-<))
     (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 16
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (16 16
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (16 16 (:REWRITE INTEGERP-<-CONSTANT))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-1))
     (16 16 (:REWRITE CONSTANT-<-INTEGERP))
     (16 16
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< c (- x))|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< (/ x) (/ y))|))
     (16 16 (:REWRITE |(< (- x) c)|))
     (16 16 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10 (:META META-RATIONALP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-TIMES-2))
     (5 5 (:REWRITE DEFAULT-TIMES-1))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (2 2 (:REWRITE |arith (* c (* d x))|))
     (1 1 (:REWRITE |arith (- (* c x))|))
     (1 1 (:REWRITE |arith (* (- x) y)|))
     (1 1
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL)))
(ACL2S::CANCEL-<-*-2
     (56 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (40 10 (:REWRITE RATIONALP-X))
     (22 16
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (16 16 (:REWRITE THE-FLOOR-BELOW))
     (16 16 (:REWRITE THE-FLOOR-ABOVE))
     (16 16 (:REWRITE SIMPLIFY-SUMS-<))
     (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 16
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (16 16
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (16 16 (:REWRITE INTEGERP-<-CONSTANT))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-1))
     (16 16 (:REWRITE CONSTANT-<-INTEGERP))
     (16 16
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< c (- x))|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< (/ x) (/ y))|))
     (16 16 (:REWRITE |(< (- x) c)|))
     (16 16 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10 (:META META-RATIONALP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-TIMES-2))
     (5 5 (:REWRITE DEFAULT-TIMES-1))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (2 2 (:REWRITE |arith (* c (* d x))|))
     (1 1 (:REWRITE |arith (- (* c x))|))
     (1 1 (:REWRITE |arith (* (- x) y)|))
     (1 1
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL)))
(ACL2S::NUMERATOR-N-DECREASES
     (537 537 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (537 537
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (57 10 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (50 10 (:REWRITE SIMPLIFY-SUMS-<))
     (50 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (33 33 (:REWRITE DEFAULT-PLUS-2))
     (33 33 (:REWRITE DEFAULT-PLUS-1))
     (30 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (30 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (8 2 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE DEFAULT-MINUS))
     (5 5 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 1
        (:INDUCTION ACL2S::POS-IND-INDUCTION-SCHEME))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(ACL2S::REPLACE-O<-WITH-<
     (26 1 (:REWRITE O<=-O-FINP-DEF))
     (25 1 (:REWRITE O-FINP-<))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 1 (:REWRITE O-FIRST-EXPT-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
     (1 1 (:REWRITE O-INFP-O-FINP-O<=))
     (1 1 (:REWRITE O-FIRST-COEFF-<))
     (1 1 (:REWRITE AC-<)))
(ACL2S::ACL2S-TRUE-LIST-UNDEFINED-TRUE-LISTP)
(ACL2S::BIN-APP-CONTRACT)
(ACL2S::BIN-APP-CONTRACT-TP)
(ACL2S::BIN-APP-CONTRACT-GENRULE)
(ACL2S::BIN-APP)
(ACL2S::BIN-APP-DEFINITION-RULE (2 1
                                   (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                                (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
                                (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(ACL2S::MOD-PLUS-SIMPLIFY-A<N-+B
     (10594 10594
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (10594 10594
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8215 2727 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (7531 2727 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (5551 2727
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (5551 2727
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (4511 2727 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (4480 168 (:LINEAR MOD-BOUNDS-2))
     (2846 2804 (:REWRITE DEFAULT-TIMES-1))
     (2824 2804 (:REWRITE DEFAULT-TIMES-2))
     (2727 2727 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2727 2727
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2727 2727
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (2727 2727
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2727 2727
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2727 2727
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2727 2727
           (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (2719 1240 (:REWRITE DEFAULT-PLUS-2))
     (2453 91 (:REWRITE ACL2S::ACL2S-CANCEL-MOD-+))
     (2401 2401
           (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (2108 391
           (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (1942 394 (:REWRITE RATIONALP-X))
     (1860 70 (:REWRITE CANCEL-MOD-+))
     (1762 82 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (1692 80 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1626 80 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1604 301
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1604 301
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1592 142 (:REWRITE |(integerp (- x))|))
     (1544 84 (:LINEAR MOD-BOUNDS-3))
     (1392 80 (:REWRITE MOD-ZERO . 3))
     (1350 1240 (:REWRITE DEFAULT-PLUS-1))
     (1308 80 (:REWRITE MOD-X-Y-=-X . 4))
     (1080 142 (:REWRITE |(* (- x) y)|))
     (1076 1076
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (888 888 (:REWRITE THE-FLOOR-BELOW))
     (888 888 (:REWRITE THE-FLOOR-ABOVE))
     (887 887
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (887 887 (:REWRITE DEFAULT-LESS-THAN-1))
     (882 882
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (865 865
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (865 865
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (865 865
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (856 856 (:REWRITE INTEGERP-<-CONSTANT))
     (856 856 (:REWRITE CONSTANT-<-INTEGERP))
     (856 856
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (856 856
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (856 856
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (856 856
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (856 856 (:REWRITE |(< c (- x))|))
     (856 856
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (856 856
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (856 856
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (856 856
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (856 856 (:REWRITE |(< (/ x) (/ y))|))
     (856 856 (:REWRITE |(< (- x) c)|))
     (856 856 (:REWRITE |(< (- x) (- y))|))
     (790 30
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (732 80 (:REWRITE MOD-ZERO . 4))
     (642 642 (:REWRITE INTEGERP-MINUS-X))
     (639 639 (:REWRITE DEFAULT-DIVIDE))
     (638 638 (:META META-INTEGERP-CORRECT))
     (636 636
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (584 584
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (406 406
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (406 406
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (403 403 (:REWRITE |(< (* x y) 0)|))
     (400 400 (:REWRITE |(< (/ x) 0)|))
     (394 394 (:REWRITE RATIONALP-MINUS-X))
     (391 391
          (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (377 149 (:REWRITE DEFAULT-MINUS))
     (359 359 (:META META-RATIONALP-CORRECT))
     (301 301
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (301 284 (:REWRITE |(equal (/ x) c)|))
     (297 297
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (297 297
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (297 297
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (284 284
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (284 284
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (284 284 (:REWRITE |(equal c (/ x))|))
     (284 284 (:REWRITE |(equal (/ x) (/ y))|))
     (284 284 (:REWRITE |(equal (- x) (- y))|))
     (283 283 (:REWRITE |(equal c (- x))|))
     (283 283 (:REWRITE |(equal (- x) c)|))
     (273 273
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (273 273
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (271 271 (:REWRITE |(< 0 (* x y))|))
     (268 70 (:REWRITE MOD-X-Y-=-X . 2))
     (267 267 (:REWRITE |(< 0 (/ x))|))
     (258 70 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (258 70
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (225 225
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (180 180 (:REWRITE O-INFP->NEQ-0))
     (178 70
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (178 70 (:REWRITE MOD-CANCEL-*-CONST))
     (178 70
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (178 70
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (169 35 (:REWRITE ACL2-NUMBERP-X))
     (161 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (142 142 (:REWRITE |(- (* c x))|))
     (108 12 (:REWRITE |arith (* 1 x)|))
     (103 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (94 94 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (91 91
         (:REWRITE ACL2S::ACL2S-DEFAULT-MOD-RATIO))
     (84 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (72 12 (:REWRITE |arith (* -1 x)|))
     (70 70
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (70 70 (:REWRITE |(mod x (- y))| . 3))
     (70 70 (:REWRITE |(mod x (- y))| . 2))
     (70 70 (:REWRITE |(mod x (- y))| . 1))
     (70 70
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (70 70 (:REWRITE |(mod (- x) y)| . 3))
     (70 70 (:REWRITE |(mod (- x) y)| . 2))
     (70 70 (:REWRITE |(mod (- x) y)| . 1))
     (70 70
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (60 12
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (60 12
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (57 57 (:REWRITE |(not (equal x (/ y)))|))
     (57 57 (:REWRITE |(equal x (/ y))|))
     (52 52 (:REWRITE |(equal (+ (- c) x) y)|))
     (36 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (36 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (36 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (36 12
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (36 12
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (36 12
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (36 12
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (36 12
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (33 9
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (32 32
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<2))
     (26 26 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (24 24 (:REWRITE |arith (* c (* d x))|))
     (21 21 (:REWRITE |(< (+ c/d x) y)|))
     (21 21 (:REWRITE |(< (+ (- c) x) y)|))
     (21 9
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (12 12 (:REWRITE |arith (- (* c x))|))
     (12 12 (:REWRITE |arith (* (- x) y)|))
     (10 10 (:REWRITE FOLD-CONSTS-IN-+))
     (8 8
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (8 8
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (4 4
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (4 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (3 3
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (3 3 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (3 3 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (2 2
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(ACL2S::MOD-PLUS-SIMPLIFY-B<N-+B
     (1565 313 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1269 313 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1032 1032
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1032 1032
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1032 1032
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1032 1032
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (877 313
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (877 313
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (700 20 (:LINEAR MOD-BOUNDS-2))
     (700 20 (:LINEAR MOD-BOUNDS-1))
     (359 64
          (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (313 313 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (313 313 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (313 313
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (313 313
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (313 313
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (313 313 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (313 313 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (313 313
          (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (308 308
          (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (279 62 (:REWRITE DEFAULT-PLUS-2))
     (252 7 (:REWRITE MOD-X-Y-=-X . 4))
     (216 61
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (216 61
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (215 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (215 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (215 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (215 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (210 10 (:LINEAR MOD-BOUNDS-3))
     (159 9 (:REWRITE ACL2S::ACL2S-CANCEL-MOD-+))
     (147 7 (:REWRITE MOD-ZERO . 3))
     (140 7 (:REWRITE MOD-ZERO . 4))
     (126 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (126 6
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (120 6 (:REWRITE MOD-X-Y-=-X . 2))
     (102 6 (:REWRITE CANCEL-MOD-+))
     (96 96 (:REWRITE THE-FLOOR-BELOW))
     (96 96 (:REWRITE THE-FLOOR-ABOVE))
     (96 96
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (95 95 (:REWRITE DEFAULT-LESS-THAN-1))
     (93 93 (:REWRITE SIMPLIFY-SUMS-<))
     (93 93
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (93 93
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (93 93
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (93 93
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (93 93 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (93 93 (:REWRITE INTEGERP-<-CONSTANT))
     (93 93 (:REWRITE CONSTANT-<-INTEGERP))
     (93 93
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (93 93
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (93 93
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (93 93
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (93 93 (:REWRITE |(< c (- x))|))
     (93 93
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (93 93
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (93 93
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (93 93
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (93 93 (:REWRITE |(< (/ x) (/ y))|))
     (93 93 (:REWRITE |(< (- x) c)|))
     (93 93 (:REWRITE |(< (- x) (- y))|))
     (92 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (73 62 (:REWRITE DEFAULT-PLUS-1))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (70 7 (:REWRITE DEFAULT-MOD-RATIO))
     (69 18 (:REWRITE RATIONALP-X))
     (64 64
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (63 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (61 61
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (56 56
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (56 56
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (56 56 (:REWRITE |(equal c (/ x))|))
     (56 56 (:REWRITE |(equal c (- x))|))
     (56 56 (:REWRITE |(equal (/ x) c)|))
     (56 56 (:REWRITE |(equal (/ x) (/ y))|))
     (56 56 (:REWRITE |(equal (- x) c)|))
     (56 56 (:REWRITE |(equal (- x) (- y))|))
     (51 51
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (43 43 (:REWRITE |(< (/ x) 0)|))
     (43 43 (:REWRITE |(< (* x y) 0)|))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (40 40 (:REWRITE |(< 0 (/ x))|))
     (40 40 (:REWRITE |(< 0 (* x y))|))
     (36 36 (:REWRITE O-INFP->NEQ-0))
     (35 35 (:REWRITE REDUCE-INTEGERP-+))
     (35 35 (:REWRITE INTEGERP-MINUS-X))
     (35 35 (:META META-INTEGERP-CORRECT))
     (30 6
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (30 6 (:REWRITE MOD-CANCEL-*-CONST))
     (30 6
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (30 6
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (29 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (26 26 (:REWRITE DEFAULT-TIMES-2))
     (26 26 (:REWRITE DEFAULT-TIMES-1))
     (25 25
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (25 25
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (25 25 (:REWRITE DEFAULT-DIVIDE))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:META META-RATIONALP-CORRECT))
     (16 1 (:REWRITE |(integerp (- x))|))
     (15 5
         (:REWRITE ACL2S::MOD-PLUS-SIMPLIFY-A<N-+B))
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (10 1 (:REWRITE |(* (- x) y)|))
     (7 7 (:REWRITE DEFAULT-MOD-2))
     (7 7 (:REWRITE DEFAULT-MOD-1))
     (6 6
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
     (6 2 (:REWRITE DEFAULT-MINUS))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(- (* c x))|)))
(ACL2S::MOD-PLUS-SIMPLIFY-A<N-+B+N
     (3983 421 (:REWRITE REDUCE-RATIONALP-*))
     (3879 3879
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (3879 3879
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (3879 3879
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2706 1270 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2307 2303 (:REWRITE DEFAULT-TIMES-2))
     (2303 2303 (:REWRITE DEFAULT-TIMES-1))
     (2298 78 (:LINEAR MOD-BOUNDS-2))
     (2134 1270 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2081 475 (:REWRITE RATIONALP-X))
     (1516 152 (:DEFINITION RFIX))
     (1270 1270 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1270 1270 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1270 1270 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1270 1270
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1270 1270
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1270 1270
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1270 1270
           (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (1270 1270
           (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (1270 1270
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1270 1270
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1270 1270
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (1270 1270
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (1270 1270
           (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (1108 388
           (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (1054 40 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (1030 40 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (888 35 (:REWRITE MOD-X-Y-=-X . 4))
     (880 40 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (817 35 (:REWRITE MOD-X-Y-=-X . 3))
     (794 794
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (792 44 (:REWRITE ACL2S::ACL2S-CANCEL-MOD-+))
     (730 254
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (730 254
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (663 39 (:LINEAR MOD-BOUNDS-3))
     (645 35 (:REWRITE CANCEL-MOD-+))
     (623 555
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (566 566 (:REWRITE THE-FLOOR-BELOW))
     (566 566 (:REWRITE THE-FLOOR-ABOVE))
     (564 564
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (555 555
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (544 544 (:REWRITE INTEGERP-MINUS-X))
     (542 542 (:META META-INTEGERP-CORRECT))
     (534 534
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (534 534
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (534 534
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (534 534 (:REWRITE INTEGERP-<-CONSTANT))
     (534 534 (:REWRITE CONSTANT-<-INTEGERP))
     (534 534
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (534 534
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (534 534
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (534 534
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (534 534 (:REWRITE |(< c (- x))|))
     (534 534
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (534 534
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (534 534
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (534 534
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (534 534 (:REWRITE |(< (/ x) (/ y))|))
     (534 534 (:REWRITE |(< (- x) c)|))
     (534 534 (:REWRITE |(< (- x) (- y))|))
     (486 54 (:REWRITE RATIONALP-/))
     (475 35 (:REWRITE MOD-ZERO . 3))
     (461 53 (:REWRITE ACL2-NUMBERP-X))
     (440 55 (:REWRITE |(integerp (- x))|))
     (440 35 (:REWRITE MOD-ZERO . 4))
     (421 421 (:REWRITE RATIONALP-MINUS-X))
     (391 391 (:META META-RATIONALP-CORRECT))
     (388 388 (:REWRITE DEFAULT-DIVIDE))
     (386 386
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (330 55 (:REWRITE |(* (- x) y)|))
     (308 284
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (277 277 (:REWRITE |(< (/ x) 0)|))
     (271 237 (:REWRITE |(equal (/ x) c)|))
     (266 238
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (254 254
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (237 237
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (237 237 (:REWRITE |(equal c (/ x))|))
     (237 237 (:REWRITE |(equal (/ x) (/ y))|))
     (237 237 (:REWRITE |(equal (- x) (- y))|))
     (235 235 (:REWRITE |(equal c (- x))|))
     (235 235 (:REWRITE |(equal (- x) c)|))
     (195 35 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (195 35
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (185 35 (:REWRITE MOD-X-Y-=-X . 2))
     (159 159 (:REWRITE O-INFP->NEQ-0))
     (142 142
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (142 142
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (140 140 (:REWRITE |(< 0 (/ x))|))
     (140 140 (:REWRITE |(< 0 (* x y))|))
     (123 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (82 82 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (63 63 (:REWRITE DEFAULT-MINUS))
     (62 18
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (55 55 (:REWRITE |(- (* c x))|))
     (54 54 (:REWRITE INTEGERP-/))
     (44 44
         (:REWRITE ACL2S::ACL2S-DEFAULT-MOD-RATIO))
     (38 38
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<2))
     (38 38 (:REWRITE |(equal (+ (- c) x) y)|))
     (36 4
         (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (36 4
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (36 4
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (36 4
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (35 35
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (35 35
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (35 35 (:REWRITE MOD-CANCEL-*-CONST))
     (35 35 (:REWRITE |(mod x (- y))| . 3))
     (35 35 (:REWRITE |(mod x (- y))| . 2))
     (35 35 (:REWRITE |(mod x (- y))| . 1))
     (35 35
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (35 35
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (35 35 (:REWRITE |(mod (- x) y)| . 3))
     (35 35 (:REWRITE |(mod (- x) y)| . 2))
     (35 35 (:REWRITE |(mod (- x) y)| . 1))
     (35 35
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (35 35
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (26 26 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (25 25 (:REWRITE |(< (+ c/d x) y)|))
     (25 25 (:REWRITE |(< (+ (- c) x) y)|))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+))
     (14 14 (:REWRITE |(not (equal x (/ y)))|))
     (14 14 (:REWRITE |(equal x (/ y))|))
     (9 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (8 8
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (8 8
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (4 1 (:REWRITE |(+ x x)|))
     (2 2 (:REWRITE |(/ (/ x))|))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1 1 (:TYPE-PRESCRIPTION ABS))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (1 1 (:REWRITE |(equal (* x y) 0)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(* a (/ a) b)|)))
(ACL2S::MOD-PLUS-SIMPLIFY-B<N-+B+N
     (5530 1110 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (4670 1110 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3961 3961
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (3961 3961
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (3961 3961
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (3150 1110
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1395 174
           (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (1196 36 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1190 36 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (1179 42 (:REWRITE ACL2S::ACL2S-CANCEL-MOD-+))
     (1110 1110
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1110 1110
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (1110 1110
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (1110 1110
           (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (1108 1108
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1098 1098
           (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (1098 36 (:REWRITE MOD-X-Y-=-X . 4))
     (1096 1096 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (692 36 (:REWRITE MOD-ZERO . 3))
     (626 36 (:REWRITE MOD-ZERO . 4))
     (626 36 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (621 21 (:REWRITE CANCEL-MOD-+))
     (613 30 (:LINEAR MOD-BOUNDS-3))
     (600 152
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (585 152
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (570 36 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (528 33 (:REWRITE |(integerp (- x))|))
     (469 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (405 39 (:REWRITE |(* (- x) y)|))
     (378 36 (:REWRITE DEFAULT-MOD-RATIO))
     (298 298 (:REWRITE THE-FLOOR-BELOW))
     (298 298 (:REWRITE THE-FLOOR-ABOVE))
     (298 298
          (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (297 297 (:REWRITE SIMPLIFY-SUMS-<))
     (297 297
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (297 297
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (297 297
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (297 297
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (297 297
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (297 297
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (297 297 (:REWRITE INTEGERP-<-CONSTANT))
     (297 297 (:REWRITE DEFAULT-LESS-THAN-1))
     (297 297 (:REWRITE CONSTANT-<-INTEGERP))
     (297 297
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (297 297
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (297 297
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (297 297
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (297 297 (:REWRITE |(< c (- x))|))
     (297 297
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (297 297
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (297 297
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (297 297
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (297 297 (:REWRITE |(< (/ x) (/ y))|))
     (297 297 (:REWRITE |(< (- x) c)|))
     (297 297 (:REWRITE |(< (- x) (- y))|))
     (249 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (249 21
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (240 21 (:REWRITE MOD-X-Y-=-X . 2))
     (226 214 (:REWRITE DEFAULT-TIMES-2))
     (225 141
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (214 214 (:REWRITE DEFAULT-TIMES-1))
     (209 53 (:REWRITE DEFAULT-MINUS))
     (203 27 (:REWRITE ACL2-NUMBERP-X))
     (191 50 (:REWRITE RATIONALP-X))
     (174 174
          (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (152 152
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (150 150
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (140 140
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (140 140
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (140 140 (:REWRITE |(< (/ x) 0)|))
     (140 140 (:REWRITE |(< (* x y) 0)|))
     (138 138 (:REWRITE REDUCE-INTEGERP-+))
     (138 138
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (138 138 (:REWRITE INTEGERP-MINUS-X))
     (138 138 (:REWRITE |(equal c (/ x))|))
     (138 138 (:REWRITE |(equal c (- x))|))
     (138 138 (:REWRITE |(equal (/ x) c)|))
     (138 138 (:REWRITE |(equal (/ x) (/ y))|))
     (138 138 (:REWRITE |(equal (- x) c)|))
     (138 138 (:REWRITE |(equal (- x) (- y))|))
     (138 138 (:META META-INTEGERP-CORRECT))
     (136 136
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (136 136 (:REWRITE DEFAULT-DIVIDE))
     (110 110
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (108 108 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (105 21
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (105 21 (:REWRITE MOD-CANCEL-*-CONST))
     (105 21
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (105 21
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (100 100
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (100 100
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (100 100 (:REWRITE |(< 0 (/ x))|))
     (100 100 (:REWRITE |(< 0 (* x y))|))
     (76 19 (:REWRITE |(* y x)|))
     (73 63 (:REWRITE O-INFP->NEQ-0))
     (59 59
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (50 50 (:REWRITE REDUCE-RATIONALP-+))
     (50 50 (:REWRITE REDUCE-RATIONALP-*))
     (50 50 (:REWRITE RATIONALP-MINUS-X))
     (50 50 (:META META-RATIONALP-CORRECT))
     (39 39 (:REWRITE |(- (* c x))|))
     (36 36 (:REWRITE DEFAULT-MOD-2))
     (36 36 (:REWRITE DEFAULT-MOD-1))
     (33 3 (:REWRITE |(* y (* x z))|))
     (29 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (21 21
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (21 21 (:REWRITE |(mod x (- y))| . 3))
     (21 21 (:REWRITE |(mod x (- y))| . 2))
     (21 21 (:REWRITE |(mod x (- y))| . 1))
     (21 21
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (21 21 (:REWRITE |(mod (- x) y)| . 3))
     (21 21 (:REWRITE |(mod (- x) y)| . 2))
     (21 21 (:REWRITE |(mod (- x) y)| . 1))
     (21 21
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (18 18 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 3 (:REWRITE |(+ x x)|))
     (9 9 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3 (:TYPE-PRESCRIPTION ABS))
     (3 3 (:REWRITE |(equal (* x y) 0)|))
     (3 3 (:REWRITE |(* a (/ a) b)|))
     (2 2
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS)))
(ACL2S::|(x*y mod m)/y = x|
 (7790 3706 (:REWRITE DEFAULT-TIMES-2))
 (6993 1481 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3307 3307
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3307 3307
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3307 3307
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2942 53 (:REWRITE ACL2S::ACL2S-CANCEL-MOD-+))
 (2610 2610
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2610 2610
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2610 2610
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2497 378 (:REWRITE RATIONALP-X))
 (2120 326 (:REWRITE REDUCE-RATIONALP-*))
 (1591 22 (:REWRITE CANCEL-MOD-+))
 (1498 764 (:META META-INTEGERP-CORRECT))
 (1497 1497 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1497 1497
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1497 1497
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1497 1497
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1497 1497
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1481 1481 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (1481 1481
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1481 1481
       (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
 (1481 1481
       (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (1481 1481
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1481 1481
       (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (1481 1481
       (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
 (1382 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1374 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1351 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1347 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1312 48 (:REWRITE |(* (- x) y)|))
 (1082 326 (:META META-RATIONALP-CORRECT))
 (1077 24 (:REWRITE MOD-ZERO . 3))
 (960 24 (:REWRITE MOD-ZERO . 4))
 (792 72 (:DEFINITION RFIX))
 (764 764 (:REWRITE REDUCE-INTEGERP-+))
 (764 764 (:REWRITE INTEGERP-MINUS-X))
 (756 36 (:REWRITE |(integerp (- x))|))
 (692 22 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (692 22
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (690 22 (:REWRITE MOD-X-Y-=-X . 2))
 (672 177
      (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
 (660 22
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (660 22 (:REWRITE MOD-CANCEL-*-CONST))
 (660 22
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (660 22
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (594 594
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (594 594 (:REWRITE DEFAULT-DIVIDE))
 (568 568 (:REWRITE |(* c (* d x))|))
 (504 100 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (468 52 (:REWRITE RATIONALP-/))
 (436 10 (:LINEAR MOD-BOUNDS-3))
 (423 47 (:REWRITE ACL2-NUMBERP-X))
 (408 100
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (408 100
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (326 326 (:REWRITE REDUCE-RATIONALP-+))
 (326 326 (:REWRITE RATIONALP-MINUS-X))
 (260 146 (:REWRITE INTEGERP-/))
 (252 180 (:REWRITE DEFAULT-LESS-THAN-1))
 (226 178 (:REWRITE SIMPLIFY-SUMS-<))
 (226 178
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (226 178
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (204 180 (:REWRITE DEFAULT-LESS-THAN-2))
 (182 182 (:REWRITE THE-FLOOR-BELOW))
 (182 182 (:REWRITE THE-FLOOR-ABOVE))
 (182 182
      (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
 (178 178
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (178 178
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (178 178
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (178 178
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (178 178 (:REWRITE INTEGERP-<-CONSTANT))
 (178 178 (:REWRITE CONSTANT-<-INTEGERP))
 (178 178
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (178 178
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (178 178
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (178 178
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (178 178 (:REWRITE |(< c (- x))|))
 (178 178
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (178 178
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (178 178
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (178 178
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (178 178 (:REWRITE |(< (/ x) (/ y))|))
 (178 178 (:REWRITE |(< (- x) c)|))
 (178 178 (:REWRITE |(< (- x) (- y))|))
 (177 177
      (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (158 78 (:REWRITE |(< (* x y) 0)|))
 (143 79 (:REWRITE |(< 0 (* x y))|))
 (113 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (101 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (101 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (101 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (100 100
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (98 98
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (98 98
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (98 98 (:REWRITE |(equal c (/ x))|))
 (98 98 (:REWRITE |(equal c (- x))|))
 (98 98 (:REWRITE |(equal (/ x) c)|))
 (98 98 (:REWRITE |(equal (/ x) (/ y))|))
 (98 98 (:REWRITE |(equal (- x) c)|))
 (98 98 (:REWRITE |(equal (- x) (- y))|))
 (92 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (87 87
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (79 79
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (79 79
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (79 79 (:REWRITE |(< 0 (/ x))|))
 (78 78
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (78 78
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (78 78 (:REWRITE |(< (/ x) 0)|))
 (76 21
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (71 55 (:REWRITE DEFAULT-MINUS))
 (68 68 (:REWRITE O-INFP->NEQ-0))
 (65 21
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (63 63 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (58 8 (:REWRITE |(+ y x)|))
 (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-3F))
 (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-2F))
 (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-1F))
 (48 48 (:REWRITE |(- (* c x))|))
 (47 47 (:REWRITE DEFAULT-MOD-2))
 (47 47 (:REWRITE DEFAULT-MOD-1))
 (41 8 (:REWRITE NORMALIZE-ADDENDS))
 (38 2 (:REWRITE |(+ y (+ x z))|))
 (34 6 (:REWRITE |(- (if a b c))|))
 (31 26 (:REWRITE DEFAULT-PLUS-1))
 (30 30
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (30
   30
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (30
  30
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (26 26 (:REWRITE DEFAULT-PLUS-2))
 (22 22
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (22 22 (:REWRITE |(mod x (- y))| . 3))
 (22 22 (:REWRITE |(mod x (- y))| . 2))
 (22 22 (:REWRITE |(mod x (- y))| . 1))
 (22 22
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (22 22 (:REWRITE |(mod (- x) y)| . 3))
 (22 22 (:REWRITE |(mod (- x) y)| . 2))
 (22 22 (:REWRITE |(mod (- x) y)| . 1))
 (22 22
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (16 16
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (15 15 (:REWRITE |(equal (* x y) 0)|))
 (13 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (6 6 (:REWRITE |(not (equal x (/ y)))|))
 (6 6 (:REWRITE |(equal x (/ y))|))
 (5 5 (:REWRITE |(+ x (- x))|))
 (5 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (4 4 (:REWRITE |(* (/ c) (expt d n))|))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE |(+ 0 x)|))
 (1 1 (:REWRITE MOD-POSITIVE . 3))
 (1 1 (:REWRITE MOD-POSITIVE . 2))
 (1 1 (:REWRITE MOD-NEGATIVE . 3))
 (1 1 (:REWRITE MOD-NEGATIVE . 2))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(ACL2S::ACL2S-BOOLEAN-UNDEFINED-BOOLEANP)
(ACL2S::IN-CONTRACT)
(ACL2S::IN-CONTRACT-TP)
(ACL2S::IN-CONTRACT-GENRULE)
(ACL2S::IN)
(ACL2S::IN-INDUCTION-SCHEME)
(ACL2S::IN-DEFINITION-RULE)
(ACL2S::NIN-CONTRACT)
(ACL2S::NIN-CONTRACT-TP)
(ACL2S::NIN-CONTRACT-GENRULE)
(ACL2S::NIN)
(ACL2S::NIN-DEFINITION-RULE)
(ACL2S::DEF=>NON-EMPTY-TRUE-LIST (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NON-EMPTY-TRUE-LIST=>DEF)
(ACL2S::LEFT)
(ACL2S::LEFT-DEFINITION-RULE)
(ACL2S::RIGHT)
(ACL2S::RIGHT-DEFINITION-RULE)
(ACL2S::HEAD)
(ACL2S::HEAD-DEFINITION-RULE)
(ACL2S::TAIL-CONTRACT
     (437 2 (:DEFINITION TRUE-LISTP))
     (156 5
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (148 2 (:DEFINITION TRUE-LIST-LISTP))
     (107 5
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (93 2
         (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (83 5
         (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (69 2 (:DEFINITION BOOLEAN-LISTP))
     (66 33
         (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (62 4 (:DEFINITION NAT-LISTP))
     (61 5
         (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (60 2 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (55 5
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (53 5
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (49 5
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (47 2 (:DEFINITION ATOM-LISTP))
     (46 2 (:DEFINITION KEYWORDP))
     (45 5
         (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (45 5
         (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (45 5
         (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (45 5
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (39 2 (:DEFINITION RATIONAL-LISTP))
     (37 2 (:DEFINITION SYMBOL-LISTP))
     (35 2 (:DEFINITION INTEGER-LISTP))
     (33 33
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (33 33
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (33 33 (:REWRITE CONSP-BY-LEN))
     (32 32 (:REWRITE DEFAULT-CDR))
     (31 2 (:DEFINITION ACL2S::POS-LISTP))
     (31 2 (:DEFINITION ACL2-NUMBER-LISTP))
     (29 29 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (29 2 (:DEFINITION STRING-LISTP))
     (29 2
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (28 28 (:REWRITE DEFAULT-CAR))
     (28 28 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (26 26 (:TYPE-PRESCRIPTION NAT-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (18 5 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (18 5
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (17 17 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (14 14 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (13 13 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (13 13 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION STRING-LISTP))
     (13 13 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (13 13 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (8 8
        (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (8 8 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 4
        (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (7 7 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (6 6 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (6 6 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (6 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 4
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 3 (:REWRITE O-P-O-INFP-CAR))
     (6 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (4 4
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>POS-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (4 4
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (3 3 (:TYPE-PRESCRIPTION O-P))
     (3 3 (:TYPE-PRESCRIPTION ALISTP))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE SET::IN-SET))
     (2 2
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::TAIL-CONTRACT-TP)
(ACL2S::TAIL-CONTRACT-GENRULE)
(ACL2S::TAIL)
(ACL2S::TAIL-DEFINITION-RULE)
(ACL2S::ACL2S-NON-EMPTY-TRUE-LIST-UNDEFINED-NON-EMPTY-TRUE-LISTP)
(ACL2S::LCONS-CONTRACT
     (1281 6 (:DEFINITION TRUE-LISTP))
     (464 15
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (440 6 (:DEFINITION TRUE-LIST-LISTP))
     (317 15
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (275 6
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (245 15
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (203 6 (:DEFINITION BOOLEAN-LISTP))
     (196 98
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (180 6 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (179 15
          (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (178 12 (:DEFINITION NAT-LISTP))
     (161 15
          (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (155 15
          (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (143 15
          (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (138 6 (:DEFINITION KEYWORDP))
     (137 6 (:DEFINITION ATOM-LISTP))
     (131 15
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (131 15
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (131 15
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (131 15
          (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (125 15
          (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (125 15
          (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (113 6 (:DEFINITION RATIONAL-LISTP))
     (107 6 (:DEFINITION SYMBOL-LISTP))
     (101 6 (:DEFINITION INTEGER-LISTP))
     (98 98
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (98 98
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (98 98 (:REWRITE CONSP-BY-LEN))
     (96 91 (:REWRITE DEFAULT-CDR))
     (89 6 (:DEFINITION ACL2S::POS-LISTP))
     (89 6 (:DEFINITION ACL2-NUMBER-LISTP))
     (84 84 (:REWRITE DEFAULT-CAR))
     (84 84 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (83 6 (:DEFINITION STRING-LISTP))
     (83 6
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (78 78 (:TYPE-PRESCRIPTION NAT-LISTP))
     (57 57 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (54 54
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (54 15
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (51 51 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (50 15 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (39 39 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (39 39 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (39 39 (:TYPE-PRESCRIPTION STRING-LISTP))
     (39 39 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (39 39 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (39 39 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (24 24
         (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (24 24 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (24 12
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (21 21 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (18 18 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (18 18 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (18 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 12
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 9 (:REWRITE O-P-O-INFP-CAR))
     (18 9 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (14 14 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (12 12
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12
         (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (12 12 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (12 12 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (12 12 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (12 12
         (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (12 12 (:REWRITE ACL2S::DEF=>POS-LIST))
     (12 12 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (12 12
         (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (12 12 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (12 12
         (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (12 12
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (9 9 (:TYPE-PRESCRIPTION O-P))
     (9 9 (:TYPE-PRESCRIPTION ALISTP))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE SET::IN-SET))
     (6 6
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (6 6 (:REWRITE ACL2-NUMBERP-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT)))
(ACL2S::LCONS-CONTRACT-TP)
(ACL2S::LCONS-CONTRACT-GENRULE)
(ACL2S::LCONS)
(ACL2S::LCONS-DEFINITION-RULE)
(ACL2S::LNTH (36 18
                 (:TYPE-PRESCRIPTION DEFDATA::NAT-LISTP--NTH--INTEGERP))
             (18 18 (:TYPE-PRESCRIPTION NAT-LISTP)))
(ACL2S::LNTH-DEFINITION-RULE
     (2 1
        (:TYPE-PRESCRIPTION DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (1 1 (:TYPE-PRESCRIPTION NAT-LISTP)))
(ACL2S::LNTHCDR-CONTRACT)
(ACL2S::LNTHCDR-CONTRACT-TP)
(ACL2S::LNTHCDR-CONTRACT-GENRULE)
(ACL2S::LNTHCDR)
(ACL2S::LNTHCDR-DEFINITION-RULE
     (2 1
        (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ACL2S::STR-ALL=>DEF)
(ACL2S::L-STR-ALLP-IMPLIES-TLP
     (1692 8 (:DEFINITION TRUE-LISTP))
     (616 20
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (584 8 (:DEFINITION TRUE-LIST-LISTP))
     (428 20
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (372 8
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (324 20
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (268 8 (:DEFINITION BOOLEAN-LISTP))
     (263 135
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (248 8 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (236 20
          (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (232 16 (:DEFINITION NAT-LISTP))
     (212 20
          (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (204 20
          (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (192 8 (:DEFINITION KEYWORDP))
     (188 20
          (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (180 8 (:DEFINITION ATOM-LISTP))
     (172 20
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (172 20
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (172 20
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (172 20
          (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (164 20
          (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (164 20
          (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (148 8 (:DEFINITION RATIONAL-LISTP))
     (140 8 (:DEFINITION SYMBOL-LISTP))
     (135 135
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 2))
     (135 135
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 1))
     (135 135 (:REWRITE CONSP-BY-LEN))
     (132 8 (:DEFINITION INTEGER-LISTP))
     (124 124 (:REWRITE DEFAULT-CDR))
     (120 120 (:REWRITE DEFAULT-CAR))
     (120 120 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (116 8 (:DEFINITION ACL2S::POS-LISTP))
     (116 8 (:DEFINITION ACL2-NUMBER-LISTP))
     (108 8 (:DEFINITION STRING-LISTP))
     (108 8
          (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (104 104 (:TYPE-PRESCRIPTION NAT-LISTP))
     (80 80
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (72 20
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (68 68 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (64 20 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (56 56 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (52 52 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (52 52 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (52 52 (:TYPE-PRESCRIPTION STRING-LISTP))
     (52 52 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (52 52
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (52 52
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (52 52 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (52 52
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (52 52 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (52 52
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (32 32
         (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (32 32 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (32 16
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (28 28 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (24 24 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (24 24 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (24 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 16
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 12 (:REWRITE O-P-O-INFP-CAR))
     (24 12 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (16 16
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (16 16 (:TYPE-PRESCRIPTION NATP))
     (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (16 16
         (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (16 16 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (16 16 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (16 16 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (16 16
         (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (16 16 (:REWRITE ACL2S::DEF=>POS-LIST))
     (16 16 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (16 16
         (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (16 16 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (16 16
         (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (16 16
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (16 16 (:REWRITE |(equal c (/ x))|))
     (16 16 (:REWRITE |(equal c (- x))|))
     (16 16 (:REWRITE |(equal (/ x) c)|))
     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
     (16 16 (:REWRITE |(equal (- x) c)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (12 12 (:TYPE-PRESCRIPTION ALISTP))
     (8 8 (:TYPE-PRESCRIPTION POSP))
     (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-X))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE SET::IN-SET))
     (8 8
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (8 8 (:REWRITE ACL2-NUMBERP-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT)))
(ACL2S::DEF=>L-STR-ALL
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (2 1
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1 1
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (1 1
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (1 1 (:REWRITE CONSP-BY-LEN)))
(ACL2S::L-STR-ALL=>DEF
     (4 2
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (3 3 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (2 2
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (2 2 (:REWRITE CONSP-BY-LEN))
     (2 2 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::ACL2S-L-STR-ALL-UNDEFINED-L-STR-ALLP)
(ACL2S::GEN-CAR-CDR-AUX-1-CONTRACT
     (456 19
          (:REWRITE ACL2S::VAR-DISJOINT-WITH-KEYS))
     (418 19 (:DEFINITION KEYWORDP))
     (114 114
          (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (96 8 (:REWRITE STR::CONSP-OF-EXPLODE))
     (84 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (72 2 (:DEFINITION BINARY-APPEND))
     (63 6 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (57 19
         (:REWRITE ACL2S::VAR-DISJOINT-WITH-BOOL))
     (45 39 (:REWRITE DEFAULT-CDR))
     (44 25
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (44 25
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (44 25
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 19
         (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (38 38 (:TYPE-PRESCRIPTION BOOLEANP))
     (30 24 (:REWRITE DEFAULT-CAR))
     (28 7
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (25 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (25 25
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (25 25
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (25 25
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (25 25
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (25 25 (:REWRITE |(equal c (/ x))|))
     (25 25 (:REWRITE |(equal c (- x))|))
     (25 25 (:REWRITE |(equal (/ x) c)|))
     (25 25 (:REWRITE |(equal (/ x) (/ y))|))
     (25 25 (:REWRITE |(equal (- x) c)|))
     (25 25 (:REWRITE |(equal (- x) (- y))|))
     (24 24 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (24 6 (:REWRITE O-P-O-INFP-CAR))
     (22 22
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (19 19 (:TYPE-PRESCRIPTION KEYWORDP))
     (19 19
         (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (19 19
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (19 19
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (17 17 (:REWRITE CONSP-BY-LEN))
     (14 14
         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (14 14 (:TYPE-PRESCRIPTION ALISTP))
     (9 1 (:REWRITE ALISTP-OF-CDR))
     (7 7
        (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (7 7 (:REWRITE ACL2S::DEF=>ALIST))
     (7 7 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (7 7 (:REWRITE ALISTP-WHEN-ATOM))
     (6 6 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP)))
(ACL2S::GEN-CAR-CDR-AUX-1-CONTRACT-TP)
(ACL2S::GEN-CAR-CDR-AUX-1-CONTRACT-GENRULE)
(ACL2S::GEN-CAR-CDR-AUX-1)
(ACL2S::GEN-CAR-CDR-AUX-1-INDUCTION-SCHEME)
(ACL2S::GEN-CAR-CDR-AUX-1-DEFINITION-RULE)
(ACL2S::GEN-CAR-CDR-AUX-CONTRACT
  (55860 5134 (:REWRITE STR::CONSP-OF-EXPLODE))
  (43711 188 (:DEFINITION TRUE-LISTP))
  (28542 1084
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
  (21928 176 (:REWRITE STR::EXPLODE-OF-IMPLODE))
  (18560 160
         (:REWRITE STR::MAKE-CHARACTER-LIST-OF-APPEND))
  (17808 7052 (:REWRITE DEFAULT-CAR))
  (15040 470
         (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
  (14288 188 (:DEFINITION TRUE-LIST-LISTP))
  (13722 9317 (:REWRITE DEFAULT-CDR))
  (12768 464
         (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-CHARACTER-LISTP))
  (10042 470
         (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
  (9593 688 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
  (9226 403 (:DEFINITION KEYWORDP))
  (9195 247 (:REWRITE APPEND-UNDER-IFF))
  (8726 188
        (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
  (8576 64 (:DEFINITION MAKE-CHARACTER-LIST))
  (7671 472
        (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
  (7614 470
        (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
  (7080 7080 (:REWRITE CAR-WHEN-ALL-EQUALP))
  (6525 6525
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
  (6525 6525
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
  (6298 188 (:DEFINITION BOOLEAN-LISTP))
  (5820 112 (:REWRITE APPEND-OF-CONS))
  (5812 188 (:DEFINITION ACL2S::PROPER-SYMBOLP))
  (5546 470
        (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
  (5531 28 (:REWRITE CAR-OF-APPEND))
  (5452 376 (:DEFINITION NAT-LISTP))
  (5160 215
        (:REWRITE ACL2S::VAR-DISJOINT-WITH-KEYS))
  (5120 160 (:DEFINITION CHARACTER-LISTP))
  (4982 470
        (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
  (4809 4406
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
  (4809 4406
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
  (4809 4406
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
  (4794 470
        (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
  (4418 470
        (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
  (4406 4406 (:REWRITE SIMPLIFY-SUMS-EQUAL))
  (4406 4406
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
  (4406 4406
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
  (4406 4406
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
  (4406 4406
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
  (4406 4406 (:REWRITE |(equal c (/ x))|))
  (4406 4406 (:REWRITE |(equal c (- x))|))
  (4406 4406 (:REWRITE |(equal (/ x) c)|))
  (4406 4406 (:REWRITE |(equal (/ x) (/ y))|))
  (4406 4406 (:REWRITE |(equal (- x) c)|))
  (4406 4406 (:REWRITE |(equal (- x) (- y))|))
  (4238 180
        (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
  (4230 188 (:DEFINITION ATOM-LISTP))
  (4080 136 (:REWRITE STR::EXPLODE-UNDER-IFF))
  (4042 470
        (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
  (4042 470
        (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
  (4042 470
        (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
  (4042 470
        (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
  (4010 4010 (:REWRITE CONSP-BY-LEN))
  (3854 470
        (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
  (3854 470
        (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
  (3704 180
        (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
  (3704 180 (:REWRITE ALISTP-WHEN-ATOM))
  (3584 592
        (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
  (3584 592
        (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
  (3478 188 (:DEFINITION RATIONAL-LISTP))
  (3290 188 (:DEFINITION SYMBOL-LISTP))
  (3114 3114
        (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
  (3102 188 (:DEFINITION INTEGER-LISTP))
  (2726 188 (:DEFINITION ACL2S::POS-LISTP))
  (2726 188 (:DEFINITION ACL2-NUMBER-LISTP))
  (2672 592
        (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
  (2538 188 (:DEFINITION STRING-LISTP))
  (2538 188
        (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
  (2444 2444 (:TYPE-PRESCRIPTION NAT-LISTP))
  (1948 1948
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
  (1749 1749 (:REWRITE CONSP-OF-CDR-BY-LEN))
  (1692 470
        (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
  (1637 688 (:REWRITE O-P-O-INFP-CAR))
  (1598 1598 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
  (1427 470 (:REWRITE TRUE-LISTP-WHEN-ATOM))
  (1222 1222
        (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
  (1222 1222 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
  (1222 1222 (:TYPE-PRESCRIPTION STRING-LISTP))
  (1222 1222
        (:TYPE-PRESCRIPTION RATIONAL-LISTP))
  (1222 1222
        (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
  (1222 1222
        (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
  (1222 1222 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (1222 1222
        (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
  (1222 1222 (:TYPE-PRESCRIPTION ATOM-LISTP))
  (1222 1222
        (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
  (1072 1072
        (:TYPE-PRESCRIPTION CHARACTER-LISTP))
  (912 912
       (:REWRITE STR::OCT-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
  (912 912
       (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
  (816 816 (:TYPE-PRESCRIPTION ALISTP))
  (800 192
       (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-ATOM))
  (752 752
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
  (752 752 (:REWRITE ACL2S::DEF=>NAT-LIST))
  (752 376
       (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
  (658 658 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
  (645 215
       (:REWRITE ACL2S::VAR-DISJOINT-WITH-BOOL))
  (618 618 (:TYPE-PRESCRIPTION BOOLEANP))
  (592 456
       (:REWRITE STR::OCT-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
  (592 456
       (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
  (592 456
       (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
  (576 288
       (:REWRITE STR::OCT-DIGIT-CHAR-LISTP-OF-CDR-WHEN-OCT-DIGIT-CHAR-LISTP))
  (576 288
       (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-OF-CDR-WHEN-HEX-DIGIT-CHAR-LISTP))
  (576 288
       (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
  (564 564
       (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
  (564 564 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
  (474 28 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
  (470 470
       (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
  (470 470
       (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
  (470 470
       (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
  (470 470
       (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
  (470 470
       (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
  (403 403
       (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
  (376 376
       (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
  (376 376
       (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
  (376 376 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
  (376 376 (:REWRITE ACL2S::DEF=>STRING-LIST))
  (376 376
       (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
  (376 376
       (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
  (376 376 (:REWRITE ACL2S::DEF=>POS-LIST))
  (376 376 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
  (376 376
       (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
  (376 376 (:REWRITE ACL2S::DEF=>ATOM-LIST))
  (376 376
       (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
  (376 188 (:REWRITE SET::NONEMPTY-MEANS-SET))
  (360 360
       (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
  (272 272
       (:REWRITE CHARACTER-LISTP-OF-EXPLODE))
  (240 240
       (:TYPE-PRESCRIPTION MAKE-CHARACTER-LIST))
  (217 217 (:REWRITE REDUCE-INTEGERP-+))
  (217 217 (:REWRITE INTEGERP-MINUS-X))
  (217 217 (:META META-INTEGERP-CORRECT))
  (215 215 (:TYPE-PRESCRIPTION KEYWORDP))
  (192 84
       (:REWRITE STR::CONSP-OF-MAKE-CHARACTER-LIST))
  (188 188 (:TYPE-PRESCRIPTION POSP))
  (188 188
       (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
  (188 188 (:REWRITE REDUCE-RATIONALP-+))
  (188 188 (:REWRITE REDUCE-RATIONALP-*))
  (188 188 (:REWRITE RATIONALP-X))
  (188 188 (:REWRITE RATIONALP-MINUS-X))
  (188 188 (:REWRITE SET::IN-SET))
  (188 188 (:REWRITE ACL2-NUMBERP-X))
  (188 188 (:META META-RATIONALP-CORRECT))
  (184 184
       (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
  (180 180 (:REWRITE ACL2S::DEF=>ALIST))
  (170 34 (:REWRITE |(+ c (+ d x))|))
  (167 163 (:REWRITE O-P-DEF-O-FINP-1))
  (153 17 (:REWRITE ALISTP-OF-CDR))
  (133 133 (:REWRITE DEFAULT-PLUS-2))
  (133 133 (:REWRITE DEFAULT-PLUS-1))
  (99 99
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
  (99 99 (:REWRITE NORMALIZE-ADDENDS))
  (89 89
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
  (89 89 (:REWRITE O-INFP->NEQ-0))
  (64 64
      (:REWRITE STR::MAKE-CHARACTER-LIST-IS-IDENTITY-UNDER-CHARLISTEQV))
  (40 40 (:REWRITE ARITH-NORMALIZE-ADDENDS))
  (34 34 (:REWRITE |(equal (+ (- c) x) y)|))
  (29 29 (:REWRITE THE-FLOOR-BELOW))
  (29 29 (:REWRITE THE-FLOOR-ABOVE))
  (29 29
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
  (29 29
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
  (29 29 (:REWRITE SIMPLIFY-SUMS-<))
  (29 29
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
  (29 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
  (29 29
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
  (29 29
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
  (29 29
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
  (29 29
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
  (29 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
  (29 29 (:REWRITE INTEGERP-<-CONSTANT))
  (29 29 (:REWRITE DEFAULT-LESS-THAN-2))
  (29 29 (:REWRITE DEFAULT-LESS-THAN-1))
  (29 29 (:REWRITE CONSTANT-<-INTEGERP))
  (29 29
      (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
  (29 29
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
  (29 29
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
  (29 29
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
  (29 29
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
  (29 29 (:REWRITE |(< c (- x))|))
  (29 29
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
  (29 29
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
  (29 29
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
  (29 29
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
  (29 29 (:REWRITE |(< (/ x) 0)|))
  (29 29 (:REWRITE |(< (/ x) (/ y))|))
  (29 29 (:REWRITE |(< (- x) c)|))
  (29 29 (:REWRITE |(< (- x) (- y))|))
  (29 29 (:REWRITE |(< (* x y) 0)|))
  (8 8
     (:TYPE-PRESCRIPTION ACL2S::GEN-CAR-CDR-AUX-1-CONTRACT-TP))
  (4 4 (:TYPE-PRESCRIPTION O-FINP))
  (2 2
     (:REWRITE ACL2S::GEN-CAR-CDR-AUX-1-CONTRACT)))
(ACL2S::GEN-CAR-CDR-AUX-CONTRACT-TP)
(ACL2S::GEN-CAR-CDR-AUX-CONTRACT-GENRULE)
(ACL2S::GEN-CAR-CDR-AUX)
(ACL2S::GEN-CAR-CDR-AUX-INDUCTION-SCHEME)
(ACL2S::GEN-CAR-CDR-AUX-DEFINITION-RULE)
(ACL2S::GEN-CAR-CDR-DEFS-FN
     (314 22 (:REWRITE STR::CONSP-OF-EXPLODE))
     (262 4 (:DEFINITION BINARY-APPEND))
     (236 4
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (168 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (130 2 (:REWRITE APPEND-UNDER-IFF))
     (60 2 (:REWRITE STR::EXPLODE-UNDER-IFF))
     (38 26 (:REWRITE DEFAULT-CDR))
     (36 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (34 22 (:REWRITE DEFAULT-CAR))
     (30 30
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (30 30
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (29 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (29 29
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (29 29
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (29 29
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (29 29 (:REWRITE |(equal c (/ x))|))
     (29 29 (:REWRITE |(equal c (- x))|))
     (29 29 (:REWRITE |(equal (/ x) c)|))
     (29 29 (:REWRITE |(equal (/ x) (/ y))|))
     (29 29 (:REWRITE |(equal (- x) c)|))
     (29 29 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (16 4
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (14 14
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (14 14
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (12 3 (:REWRITE O-P-O-INFP-CAR))
     (10 8
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (9 1 (:REWRITE ALISTP-OF-CDR))
     (8 8
        (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (8 8 (:TYPE-PRESCRIPTION ALISTP))
     (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (6 6 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (6 6 (:REWRITE CONSP-BY-LEN))
     (4 4
        (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (4 4 (:REWRITE ACL2S::DEF=>ALIST))
     (4 4
        (:REWRITE CAR-OF-STRING-LIST-FIX-X-NORMALIZE-CONST-UNDER-STREQV))
     (4 4 (:REWRITE ALISTP-WHEN-ATOM))
     (3 3 (:REWRITE O-P-DEF-O-FINP-1))
     (3 3 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (2 2
        (:TYPE-PRESCRIPTION STRING-APPEND-LST)))
(ACL2S::GEN-CAR-CDR-DEFS-FN-INDUCTION-SCHEME)
(ACL2S::GEN-CAR-CDR-DEFS-FN-DEFINITION-RULE)
(ACL2S::GEN-CAR-CDR-MACROS-FN)
(ACL2S::GEN-CAR-CDR-MACROS-FN-DEFINITION-RULE)
(ACL2S::EXPAND-LEN-WITH-TRIGGER-CDR
     (2140 8 (:DEFINITION ACL2-COUNT))
     (1316 8 (:DEFINITION ACL2S-SIZE))
     (1160 24 (:DEFINITION INTEGER-ABS))
     (1152 16 (:DEFINITION LENGTH))
     (887 62 (:REWRITE LEN-WHEN-ATOM))
     (752 48 (:REWRITE STR::CONSP-OF-EXPLODE))
     (512 16 (:REWRITE NUMERATOR-NEGATIVE))
     (373 151 (:REWRITE DEFAULT-PLUS-2))
     (351 151 (:REWRITE DEFAULT-PLUS-1))
     (280 8 (:REWRITE |(+ (if a b c) x)|))
     (216 24 (:REWRITE |(+ y x)|))
     (212 90
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (188 8 (:DEFINITION CONS-SIZE))
     (144 144
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (126 43 (:REWRITE DEFAULT-LESS-THAN-1))
     (125 77 (:REWRITE DEFAULT-CDR))
     (119 119
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (119 119 (:REWRITE NORMALIZE-ADDENDS))
     (104 24 (:REWRITE DEFAULT-MINUS))
     (96 96 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (96 96
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (96 96
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (96 96
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (96 96
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (90 90
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (90 90
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (74 74 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (74 74 (:REWRITE CONSP-BY-LEN))
     (64 16 (:REWRITE RATIONALP-X))
     (48 48 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (48 48
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (48 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (48 48
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (48 48
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (48 48
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (48 48
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (48 48 (:REWRITE |(equal c (/ x))|))
     (48 48 (:REWRITE |(equal c (- x))|))
     (48 48 (:REWRITE |(equal (/ x) c)|))
     (48 48 (:REWRITE |(equal (/ x) (/ y))|))
     (48 48 (:REWRITE |(equal (- x) c)|))
     (48 48 (:REWRITE |(equal (- x) (- y))|))
     (47 47 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (43 43 (:REWRITE THE-FLOOR-BELOW))
     (43 43 (:REWRITE THE-FLOOR-ABOVE))
     (43 43 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (43 43
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (43 43 (:REWRITE DEFAULT-LESS-THAN-2))
     (43 43
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-<))
     (40 16 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (32 32 (:REWRITE REDUCE-INTEGERP-+))
     (32 32 (:REWRITE INTEGERP-MINUS-X))
     (32 32 (:REWRITE FOLD-CONSTS-IN-+))
     (32 32 (:REWRITE |(+ c (+ d x))|))
     (32 32 (:META META-INTEGERP-CORRECT))
     (32 16
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (30 27 (:REWRITE SIMPLIFY-SUMS-<))
     (30 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 27 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (27 27
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (27 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 27
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26 (:REWRITE CONSTANT-<-INTEGERP))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< c (- x))|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< (/ x) (/ y))|))
     (26 26 (:REWRITE |(< (- x) c)|))
     (26 26 (:REWRITE |(< (- x) (- y))|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE DEFAULT-CAR))
     (24 24 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (16 16 (:REWRITE REDUCE-RATIONALP-+))
     (16 16 (:REWRITE REDUCE-RATIONALP-*))
     (16 16 (:REWRITE RATIONALP-MINUS-X))
     (16 16
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (16 16
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (16 16 (:META META-RATIONALP-CORRECT))
     (10 10 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (8 8 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (8 8 (:REWRITE DEFAULT-REALPART))
     (8 8
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (8 8 (:REWRITE DEFAULT-IMAGPART))
     (4 4
        (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (4 4
        (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 4 (:LINEAR CONS-SIZE-WHEN-MEMBER))
     (4 4 (:LINEAR ACL2S-SIZE-WHEN-MEMBER))
     (4 4 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
     (2 2 (:LINEAR INDEX-OF-<-LEN))
     (2 2
        (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<2))
     (1 1
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-<1))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (if a b c) x)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(ACL2S::LEN-NON-NIL-WITH-TRIGGER-CDR)
(ACL2S::CDDR-IMPLIES-CDR-TRIGGER-CDDR)
(ACL2S::TLP-IMPLIES-TLPCDR-TRIGGER-CDR)
(ACL2S::TLP-CONSP-CDR-IMPLIES-TAIL-TRIGGER-TAIL
     (500 14
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (485 5 (:DEFINITION TRUE-LIST-LISTP))
     (292 14
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (257 5
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (243 14
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (227 14
          (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (208 6 (:DEFINITION BOOLEAN-LISTP))
     (192 5 (:DEFINITION ACL2S::L-STR-ALLP))
     (150 14
          (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (150 5 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (134 10 (:DEFINITION NAT-LISTP))
     (128 14
          (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (126 14
          (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (120 120 (:REWRITE DEFAULT-CDR))
     (115 5 (:DEFINITION KEYWORDP))
     (115 5 (:DEFINITION ATOM-LISTP))
     (114 14
          (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (105 5 (:DEFINITION ACL2S::STR-ALLP))
     (104 104 (:REWRITE DEFAULT-CAR))
     (104 104 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (102 14
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (102 14
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (102 14
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (102 14
          (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (96 14
         (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (96 14
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (91 5 (:DEFINITION RATIONAL-LISTP))
     (85 5 (:DEFINITION SYMBOL-LISTP))
     (79 5 (:DEFINITION INTEGER-LISTP))
     (69 69
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (69 69
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (68 68 (:REWRITE CONSP-BY-LEN))
     (67 5 (:DEFINITION ACL2S::POS-LISTP))
     (67 5 (:DEFINITION ACL2-NUMBER-LISTP))
     (64 64 (:TYPE-PRESCRIPTION NAT-LISTP))
     (61 5 (:DEFINITION STRING-LISTP))
     (61 5
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (54 54
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (48 48 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (44 14
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (32 32 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (32 32 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (32 32 (:TYPE-PRESCRIPTION STRING-LISTP))
     (32 32 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (32 32 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (32 32 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (32 16 (:REWRITE O-P-O-INFP-CAR))
     (32 16 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (26 14 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (24 24
         (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (21 21 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (20 20 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (20 10
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (19 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (19 13
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (19 13
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (18 18 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (18 18 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (16 16 (:TYPE-PRESCRIPTION ALISTP))
     (15 15 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (13 13
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (13 13
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (13 13
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (13 13
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (13 13 (:REWRITE |(equal c (/ x))|))
     (13 13 (:REWRITE |(equal c (- x))|))
     (13 13 (:REWRITE |(equal (/ x) c)|))
     (13 13 (:REWRITE |(equal (/ x) (/ y))|))
     (13 13 (:REWRITE |(equal (- x) c)|))
     (13 13 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (10 10
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (10 10
         (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (10 10
         (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>POS-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (10 10 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (10 10
         (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (10 10
         (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (6 6 (:REWRITE ACL2-NUMBERP-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (4 4 (:REWRITE SET::IN-SET)))
(ACL2S::TLP-CONSP-IMPLIES-TLP-TAIL-TRIGGER-TAIL)
(ACL2S::CONSP-CDR-IMPLIES-RIGHT-TRIGGER-RIGHT
     (12 2 (:REWRITE DEFAULT-CDR))
     (8 4
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (4 4
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (4 4
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (4 4 (:REWRITE CONSP-BY-LEN))
     (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN)))
(ACL2S::TLP-CONSP-IMPLIES-TLP-RIGHT-TRIGGER-RIGHT
     (465 2 (:DEFINITION TRUE-LISTP))
     (160 5
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (152 2 (:DEFINITION TRUE-LIST-LISTP))
     (105 5
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (91 2
         (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (83 5
         (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (81 5
         (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (76 38
         (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (69 2 (:DEFINITION ACL2S::L-STR-ALLP))
     (67 2 (:DEFINITION BOOLEAN-LISTP))
     (60 2 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (59 5
         (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (58 4 (:DEFINITION NAT-LISTP))
     (53 5
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (51 5
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (47 5
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (46 2 (:DEFINITION KEYWORDP))
     (45 2 (:DEFINITION ATOM-LISTP))
     (43 5
         (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (43 5
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (42 2 (:DEFINITION ACL2S::STR-ALLP))
     (41 5
         (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (41 5
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (39 39 (:REWRITE DEFAULT-CDR))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (38 38 (:REWRITE CONSP-BY-LEN))
     (37 2 (:DEFINITION RATIONAL-LISTP))
     (35 2 (:DEFINITION SYMBOL-LISTP))
     (33 2 (:DEFINITION INTEGER-LISTP))
     (32 32 (:REWRITE DEFAULT-CAR))
     (32 32 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (29 2 (:DEFINITION ACL2S::POS-LISTP))
     (29 2 (:DEFINITION ACL2-NUMBER-LISTP))
     (27 2 (:DEFINITION STRING-LISTP))
     (27 2
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (26 26 (:TYPE-PRESCRIPTION NAT-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (18 5
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (17 17 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (17 17 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (16 5 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (13 13 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (13 13 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION STRING-LISTP))
     (13 13 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (13 13 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (10 5 (:REWRITE O-P-O-INFP-CAR))
     (10 5 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (8 8
        (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (8 8 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 4
        (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (7 7 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (6 6 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (6 6 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (6 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 4
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:TYPE-PRESCRIPTION O-P))
     (5 5 (:TYPE-PRESCRIPTION ALISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (4 4
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>POS-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (4 4 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (4 4
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE SET::IN-SET))
     (2 2
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::LEFT-CONS (1 1 (:REWRITE DEFAULT-CAR))
                  (1 1 (:REWRITE CAR-WHEN-ALL-EQUALP)))
(ACL2S::RIGHT-CONS (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::LEFT-CONSP
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (2 1
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (1 1
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (1 1
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (1 1 (:REWRITE CONSP-BY-LEN)))
(ACL2S::RIGHT-CONSP
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 1
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (1 1
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (1 1
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (1 1 (:REWRITE CONSP-BY-LEN)))
(ACL2S::HEAD-CONS
     (465 2 (:DEFINITION TRUE-LISTP))
     (160 5
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (152 2 (:DEFINITION TRUE-LIST-LISTP))
     (105 5
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (91 2
         (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (83 5
         (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (81 5
         (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (76 38
         (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (69 2 (:DEFINITION ACL2S::L-STR-ALLP))
     (67 2 (:DEFINITION BOOLEAN-LISTP))
     (60 2 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (59 5
         (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (58 4 (:DEFINITION NAT-LISTP))
     (53 5
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (51 5
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (47 5
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (46 2 (:DEFINITION KEYWORDP))
     (45 2 (:DEFINITION ATOM-LISTP))
     (43 5
         (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (43 5
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (42 2 (:DEFINITION ACL2S::STR-ALLP))
     (41 5
         (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (41 5
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (38 38 (:REWRITE DEFAULT-CDR))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (38 38 (:REWRITE CONSP-BY-LEN))
     (37 2 (:DEFINITION RATIONAL-LISTP))
     (35 2 (:DEFINITION SYMBOL-LISTP))
     (33 33 (:REWRITE DEFAULT-CAR))
     (33 33 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (33 2 (:DEFINITION INTEGER-LISTP))
     (29 2 (:DEFINITION ACL2S::POS-LISTP))
     (29 2 (:DEFINITION ACL2-NUMBER-LISTP))
     (27 2 (:DEFINITION STRING-LISTP))
     (27 2
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (26 26 (:TYPE-PRESCRIPTION NAT-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (18 5
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (17 17 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (17 17 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (16 5 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (13 13 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (13 13 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION STRING-LISTP))
     (13 13 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (13 13 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (10 5 (:REWRITE O-P-O-INFP-CAR))
     (10 5 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (8 8
        (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (8 8 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 4
        (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (7 7 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (6 6 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (6 6 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (6 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 4
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:TYPE-PRESCRIPTION O-P))
     (5 5 (:TYPE-PRESCRIPTION ALISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (4 4
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>POS-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (4 4 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (4 4
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE SET::IN-SET))
     (2 2
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::TAIL-CONS
     (465 2 (:DEFINITION TRUE-LISTP))
     (160 5
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (152 2 (:DEFINITION TRUE-LIST-LISTP))
     (105 5
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (91 2
         (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (83 5
         (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (81 5
         (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (76 38
         (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (69 2 (:DEFINITION ACL2S::L-STR-ALLP))
     (67 2 (:DEFINITION BOOLEAN-LISTP))
     (60 2 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (59 5
         (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (58 4 (:DEFINITION NAT-LISTP))
     (53 5
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (51 5
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (47 5
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (46 2 (:DEFINITION KEYWORDP))
     (45 2 (:DEFINITION ATOM-LISTP))
     (43 5
         (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (43 5
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (42 2 (:DEFINITION ACL2S::STR-ALLP))
     (41 5
         (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (41 5
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (39 39 (:REWRITE DEFAULT-CDR))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (38 38 (:REWRITE CONSP-BY-LEN))
     (37 2 (:DEFINITION RATIONAL-LISTP))
     (35 2 (:DEFINITION SYMBOL-LISTP))
     (33 2 (:DEFINITION INTEGER-LISTP))
     (32 32 (:REWRITE DEFAULT-CAR))
     (32 32 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (29 2 (:DEFINITION ACL2S::POS-LISTP))
     (29 2 (:DEFINITION ACL2-NUMBER-LISTP))
     (27 2 (:DEFINITION STRING-LISTP))
     (27 2
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (26 26 (:TYPE-PRESCRIPTION NAT-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (18 5
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (17 17 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (17 17 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (16 5 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (13 13 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (13 13 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION STRING-LISTP))
     (13 13 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (13 13 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (10 5 (:REWRITE O-P-O-INFP-CAR))
     (10 5 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (8 8
        (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (8 8 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 4
        (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (7 7 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (6 6 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (6 6 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (6 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 4
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:TYPE-PRESCRIPTION O-P))
     (5 5 (:TYPE-PRESCRIPTION ALISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (4 4
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>POS-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (4 4 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (4 4
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE SET::IN-SET))
     (2 2
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::HEAD-CONSP
     (465 2 (:DEFINITION TRUE-LISTP))
     (160 5
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (152 2 (:DEFINITION TRUE-LIST-LISTP))
     (105 5
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (91 2
         (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (83 5
         (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (81 5
         (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (76 38
         (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (69 2 (:DEFINITION ACL2S::L-STR-ALLP))
     (67 2 (:DEFINITION BOOLEAN-LISTP))
     (60 2 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (59 5
         (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (58 4 (:DEFINITION NAT-LISTP))
     (53 5
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (51 5
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (47 5
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (46 2 (:DEFINITION KEYWORDP))
     (45 2 (:DEFINITION ATOM-LISTP))
     (43 5
         (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (43 5
         (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (43 5
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (42 2 (:DEFINITION ACL2S::STR-ALLP))
     (41 5
         (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (41 5
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (39 39 (:REWRITE DEFAULT-CDR))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (38 38 (:REWRITE CONSP-BY-LEN))
     (37 2 (:DEFINITION RATIONAL-LISTP))
     (35 2 (:DEFINITION SYMBOL-LISTP))
     (34 34 (:REWRITE DEFAULT-CAR))
     (34 34 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (33 2 (:DEFINITION INTEGER-LISTP))
     (29 2 (:DEFINITION ACL2S::POS-LISTP))
     (29 2 (:DEFINITION ACL2-NUMBER-LISTP))
     (27 2 (:DEFINITION STRING-LISTP))
     (27 2
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (26 26 (:TYPE-PRESCRIPTION NAT-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (18 5
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (17 17 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (17 17 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (16 5 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (13 13 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (13 13 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION STRING-LISTP))
     (13 13 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (13 13 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (10 5 (:REWRITE O-P-O-INFP-CAR))
     (10 5 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (8 8
        (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (8 8 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 4
        (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (7 7 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (6 6 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (6 6 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (6 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 4
        (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:TYPE-PRESCRIPTION O-P))
     (5 5 (:TYPE-PRESCRIPTION ALISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (5 5
        (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (4 4
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>POS-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (4 4 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (4 4 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (4 4
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (4 4
        (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE SET::IN-SET))
     (2 2
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::TAIL-CONSP
     (518 14
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (503 5 (:DEFINITION TRUE-LIST-LISTP))
     (310 14
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (275 5
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (267 14
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (245 14
          (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (232 6 (:DEFINITION BOOLEAN-LISTP))
     (228 114
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (210 5 (:DEFINITION ACL2S::L-STR-ALLP))
     (170 10 (:DEFINITION NAT-LISTP))
     (168 14
          (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (150 5 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (146 14
          (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (144 14
          (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (133 5 (:DEFINITION ATOM-LISTP))
     (132 14
          (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (120 120 (:REWRITE DEFAULT-CDR))
     (120 14
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (120 14
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (120 14
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (120 14
          (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (115 5 (:DEFINITION KEYWORDP))
     (114 114
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 2))
     (114 114
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 1))
     (114 114 (:REWRITE CONSP-BY-LEN))
     (114 14
          (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (114 14
          (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (109 5 (:DEFINITION RATIONAL-LISTP))
     (105 5 (:DEFINITION ACL2S::STR-ALLP))
     (104 104 (:REWRITE DEFAULT-CAR))
     (104 104 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (103 5 (:DEFINITION SYMBOL-LISTP))
     (97 5 (:DEFINITION INTEGER-LISTP))
     (85 5 (:DEFINITION ACL2S::POS-LISTP))
     (85 5 (:DEFINITION ACL2-NUMBER-LISTP))
     (79 5 (:DEFINITION STRING-LISTP))
     (79 5
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (67 67 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (64 64 (:TYPE-PRESCRIPTION NAT-LISTP))
     (54 54
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (48 48 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (44 14
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (38 14 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (32 32 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (32 32 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (32 32 (:TYPE-PRESCRIPTION STRING-LISTP))
     (32 32 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (32 32 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (32 32 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (32 16 (:REWRITE O-P-O-INFP-CAR))
     (32 16 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (24 24
         (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (20 20 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (20 10
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (19 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (19 13
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (19 13
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (18 18 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (18 18 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (16 16 (:TYPE-PRESCRIPTION O-P))
     (16 16 (:TYPE-PRESCRIPTION ALISTP))
     (15 15 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (13 13
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (13 13
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (13 13
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (13 13
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (13 13 (:REWRITE |(equal c (/ x))|))
     (13 13 (:REWRITE |(equal c (- x))|))
     (13 13 (:REWRITE |(equal (/ x) c)|))
     (13 13 (:REWRITE |(equal (/ x) (/ y))|))
     (13 13 (:REWRITE |(equal (- x) c)|))
     (13 13 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (10 10
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (10 10
         (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (10 10
         (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>POS-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (10 10 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (10 10
         (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (10 10 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (10 10
         (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (6 6 (:REWRITE ACL2-NUMBERP-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (4 4 (:REWRITE SET::IN-SET)))
(ACL2S::SNOC-CONTRACT
     (1679 6 (:DEFINITION TRUE-LISTP))
     (620 15
          (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (584 6 (:DEFINITION TRUE-LIST-LISTP))
     (359 15
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (315 120
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (305 15
          (:REWRITE ACL2S::L-STR-ALLP-IMPLIES-TLP))
     (299 6
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (291 15
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (245 6 (:DEFINITION ACL2S::L-STR-ALLP))
     (231 6 (:DEFINITION BOOLEAN-LISTP))
     (225 15
          (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (218 12 (:DEFINITION NAT-LISTP))
     (199 15
          (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (193 15
          (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (181 15
          (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (180 6 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (173 15
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (171 15
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (169 15
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (169 15
          (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (167 15
          (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (165 6 (:DEFINITION ATOM-LISTP))
     (163 15
          (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (138 6 (:DEFINITION ACL2S::STR-ALLP))
     (138 6 (:DEFINITION KEYWORDP))
     (133 6 (:DEFINITION RATIONAL-LISTP))
     (130 117 (:REWRITE DEFAULT-CDR))
     (127 6 (:DEFINITION SYMBOL-LISTP))
     (121 6 (:DEFINITION INTEGER-LISTP))
     (120 120
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 2))
     (120 120
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 1))
     (116 116 (:REWRITE CONSP-BY-LEN))
     (113 6 (:DEFINITION ACL2S::POS-LISTP))
     (109 6 (:DEFINITION ACL2-NUMBER-LISTP))
     (107 6
          (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (103 6 (:DEFINITION STRING-LISTP))
     (97 97 (:REWRITE DEFAULT-CAR))
     (97 97 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (78 78 (:TYPE-PRESCRIPTION NAT-LISTP))
     (70 15
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (67 67 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (60 15 (:REWRITE TRUE-LISTP-WHEN-ATOM))
     (54 54
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (51 51 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (40 15 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (39 39 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
     (39 39 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (39 39 (:TYPE-PRESCRIPTION STRING-LISTP))
     (39 39 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::L-STR-ALLP))
     (39 39 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (39 39 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (39 39
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (30 24 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (30 15 (:REWRITE O-P-O-INFP-CAR))
     (24 24
         (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
     (24 12
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (21 21 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (20 18 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (18 18 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (18 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 12
         (:REWRITE ACL2S::ACL2S-PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 15 (:TYPE-PRESCRIPTION O-P))
     (15 15 (:TYPE-PRESCRIPTION ALISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
     (15 15 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (14 12
         (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
     (14 12 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (14 12 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (14 12 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (14 12
         (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (14 12 (:REWRITE ACL2S::DEF=>POS-LIST))
     (14 12 (:REWRITE ACL2S::DEF=>L-STR-ALL))
     (14 12 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (14 12
         (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (14 12 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (14 12
         (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (12 12
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12
         (:REWRITE ACL2S::ACL2S-REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (12 1 (:DEFINITION BINARY-APPEND))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE SET::IN-SET))
     (6 6
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (6 6 (:REWRITE ACL2-NUMBERP-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 1
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV)))
(ACL2S::SNOC-CONTRACT-TP)
(ACL2S::SNOC-CONTRACT-GENRULE)
(ACL2S::SNOC)
(ACL2S::SNOC-DEFINITION-RULE)
(ACL2S::SNOCL-CONTRACT)
(ACL2S::SNOCL-CONTRACT-TP)
(ACL2S::SNOCL-CONTRACT-GENRULE)
(ACL2S::SNOCL)
(ACL2S::SNOCL-DEFINITION-RULE)
(ACL2S::SNOCR)
(ACL2S::SNOCR-DEFINITION-RULE (2 2 (:TYPE-PRESCRIPTION LAST)))
(ACL2S::SNOC-CONSTRUCTOR-PRED)
(ACL2S::SNOC-CONSTRUCTOR-DESTRUCTORS)
(ACL2S::LENDP-CONTRACT)
(ACL2S::LENDP-CONTRACT-TP)
(ACL2S::LENDP-CONTRACT-GENRULE)
(ACL2S::LENDP)
(ACL2S::LENDP-DEFINITION-RULE)
(ACL2S::LLEN-CONTRACT)
(ACL2S::LLEN-CONTRACT-TP)
(ACL2S::LLEN-CONTRACT-GENRULE)
(ACL2S::LLEN)
(ACL2S::LLEN-DEFINITION-RULE)
(ACL2S::LREV-CONTRACT)
(ACL2S::LREV-CONTRACT-TP)
(ACL2S::LREV-CONTRACT-GENRULE)
(ACL2S::LREV)
(ACL2S::LREV-DEFINITION-RULE)
