(BEFORE-INCLUDING-ARITHMETIC-5)
(RTL::FL (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
         (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
         (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
         (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
         (5 5
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)))
(RTL::FL-DEFAULT (76 28 (:REWRITE DEFAULT-TIMES-1))
                 (76 4 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
                 (38 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                 (28 28 (:REWRITE DEFAULT-TIMES-2))
                 (28 7 (:REWRITE RATIONALP-X))
                 (28 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                 (18 18 (:REWRITE ACL2-NUMBERP-X))
                 (13 13 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                 (13 13 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                 (13 13 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                 (13 13 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                 (13 13
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                 (9 9 (:REWRITE REDUCE-INTEGERP-+))
                 (9 9 (:REWRITE INTEGERP-MINUS-X))
                 (9 9 (:META META-INTEGERP-CORRECT))
                 (7 7 (:REWRITE REDUCE-RATIONALP-+))
                 (7 7 (:REWRITE REDUCE-RATIONALP-*))
                 (7 7 (:REWRITE RATIONALP-MINUS-X))
                 (7 7 (:META META-RATIONALP-CORRECT))
                 (2 2 (:REWRITE DEFAULT-FLOOR-2)))
(RTL::FL-DEF
     (185 5 (:REWRITE FLOOR-ZERO . 3))
     (155 5 (:REWRITE FLOOR-ZERO . 5))
     (155 5 (:REWRITE FLOOR-ZERO . 4))
     (150 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (135 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (80 80 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (80 80 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (80 80 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (80 80 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (80 80
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (75 5 (:REWRITE CANCEL-FLOOR-+))
     (69 69 (:REWRITE DEFAULT-TIMES-2))
     (69 69 (:REWRITE DEFAULT-TIMES-1))
     (62 28 (:REWRITE SIMPLIFY-SUMS-<))
     (62 28
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (62 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (62 28 (:REWRITE DEFAULT-LESS-THAN-2))
     (50 5 (:REWRITE FLOOR-=-X/Y . 3))
     (50 5 (:REWRITE FLOOR-=-X/Y . 2))
     (40 5 (:REWRITE |(* (- x) y)|))
     (35 5 (:REWRITE DEFAULT-FLOOR-RATIO))
     (34 28 (:REWRITE THE-FLOOR-BELOW))
     (28 28 (:REWRITE THE-FLOOR-ABOVE))
     (28 28
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (28 28
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (28 28 (:REWRITE INTEGERP-<-CONSTANT))
     (28 28 (:REWRITE DEFAULT-LESS-THAN-1))
     (28 28 (:REWRITE CONSTANT-<-INTEGERP))
     (28 28
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (28 28
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (28 28
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (28 28
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (28 28 (:REWRITE |(< c (- x))|))
     (28 28
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (28 28
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (28 28
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (28 28
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (28 28 (:REWRITE |(< (/ x) (/ y))|))
     (28 28 (:REWRITE |(< (- x) c)|))
     (28 28 (:REWRITE |(< (- x) (- y))|))
     (27 27 (:REWRITE REDUCE-INTEGERP-+))
     (27 27 (:REWRITE INTEGERP-MINUS-X))
     (27 27 (:META META-INTEGERP-CORRECT))
     (26 1 (:REWRITE JUSTIFY-FLOOR-RECURSION))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 5 (:REWRITE |(integerp (- x))|))
     (20 5 (:REWRITE |(floor x 1)|))
     (20 3 (:REWRITE DEFAULT-PLUS-2))
     (20 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (20 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE FLOOR-ZERO . 2))
     (5 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (5 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (5 5
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 5
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (5 5 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 5 (:REWRITE DEFAULT-MINUS))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE DEFAULT-FLOOR-1))
     (5 5 (:REWRITE |(floor x (- y))| . 2))
     (5 5 (:REWRITE |(floor x (- y))| . 1))
     (5 5
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (5 5
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (5 5 (:REWRITE |(floor (- x) y)| . 2))
     (5 5 (:REWRITE |(floor (- x) y)| . 1))
     (5 5
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (5 5
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::FL-UNIQUE (4 2 (:REWRITE DEFAULT-PLUS-2))
                (2 2
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (2 2 (:REWRITE NORMALIZE-ADDENDS))
                (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::FL-INTEGERP (11 3 (:REWRITE ACL2-NUMBERP-X))
                  (11 1
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (4 2 (:REWRITE DEFAULT-PLUS-2))
                  (4 1 (:REWRITE RATIONALP-X))
                  (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (3 1
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (2 2 (:REWRITE REDUCE-INTEGERP-+))
                  (2 2
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (2 2 (:REWRITE NORMALIZE-ADDENDS))
                  (2 2 (:REWRITE INTEGERP-MINUS-X))
                  (2 2 (:REWRITE DEFAULT-PLUS-1))
                  (2 2 (:META META-INTEGERP-CORRECT))
                  (1 1 (:REWRITE REDUCE-RATIONALP-+))
                  (1 1 (:REWRITE REDUCE-RATIONALP-*))
                  (1 1
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (1 1
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE RATIONALP-MINUS-X))
                  (1 1
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (1 1 (:REWRITE |(equal c (/ x))|))
                  (1 1 (:REWRITE |(equal c (- x))|))
                  (1 1 (:REWRITE |(equal (/ x) c)|))
                  (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                  (1 1 (:REWRITE |(equal (- x) c)|))
                  (1 1 (:REWRITE |(equal (- x) (- y))|))
                  (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::INTEGERP-FL)
(RTL::QUOT-BND
     (2042 2042
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2042 2042
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2042 2042
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (948 120 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (737 121
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (737 121
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (736 120
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (461 121
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (461 121
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (461 121
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (461 121
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (460 120 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (460 120
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (460 120
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (460 120
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (440 56 (:REWRITE DEFAULT-TIMES-2))
     (411 27 (:REWRITE DEFAULT-LESS-THAN-2))
     (338 25
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (338 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (310 25 (:REWRITE SIMPLIFY-SUMS-<))
     (287 4 (:REWRITE FLOOR-ZERO . 3))
     (240 48
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (171 4 (:REWRITE CANCEL-FLOOR-+))
     (170 4 (:REWRITE FLOOR-ZERO . 5))
     (156 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (154 4 (:REWRITE FLOOR-ZERO . 4))
     (95 4 (:REWRITE FLOOR-=-X/Y . 3))
     (95 4 (:REWRITE FLOOR-=-X/Y . 2))
     (80 56 (:REWRITE DEFAULT-TIMES-1))
     (67 5 (:REWRITE DEFAULT-FLOOR-RATIO))
     (64 4 (:REWRITE |(integerp (- x))|))
     (53 4 (:REWRITE |(* (- x) y)|))
     (51 27 (:REWRITE DEFAULT-LESS-THAN-1))
     (50 5 (:REWRITE |(* (* x y) z)|))
     (27 27 (:REWRITE THE-FLOOR-BELOW))
     (27 27 (:REWRITE THE-FLOOR-ABOVE))
     (26 26
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (26 26
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 26
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
     (25 25
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 6 (:REWRITE RATIONALP-X))
     (24 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (20 4 (:REWRITE FLOOR-ZERO . 2))
     (20 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (20 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (20 4
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (20 4 (:REWRITE FLOOR-CANCEL-*-CONST))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (19 19 (:REWRITE REDUCE-INTEGERP-+))
     (19 19 (:REWRITE INTEGERP-MINUS-X))
     (19 19 (:META META-INTEGERP-CORRECT))
     (17 17
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (17 17 (:REWRITE DEFAULT-DIVIDE))
     (16 4
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (16 1 (:REWRITE |(floor x 1)|))
     (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (15 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (15 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (9 5 (:REWRITE DEFAULT-FLOOR-1))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (7 1 (:REWRITE |(* (if a b c) x)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (6 6
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(floor x (- y))| . 2))
     (4 4 (:REWRITE |(floor x (- y))| . 1))
     (4 4
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(floor (- x) y)| . 2))
     (4 4 (:REWRITE |(floor (- x) y)| . 1))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(- (* c x))|))
     (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (3 3
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|)))
(RTL::FL-MONOTONE-LINEAR (16 4 (:REWRITE RTL::INTEGERP-FL))
                         (4 4 (:REWRITE REDUCE-INTEGERP-+))
                         (4 4 (:REWRITE INTEGERP-MINUS-X))
                         (4 4 (:META META-INTEGERP-CORRECT))
                         (4 2 (:REWRITE DEFAULT-PLUS-2))
                         (2 2
                            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                         (2 2 (:REWRITE NORMALIZE-ADDENDS))
                         (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::N<=FL-LINEAR (1 1 (:REWRITE REDUCE-INTEGERP-+))
                   (1 1 (:REWRITE INTEGERP-MINUS-X))
                   (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::FL+INT-REWRITE (50 11 (:REWRITE RTL::INTEGERP-FL))
                     (16 10 (:REWRITE DEFAULT-PLUS-2))
                     (13 13 (:REWRITE REDUCE-INTEGERP-+))
                     (13 13 (:REWRITE INTEGERP-MINUS-X))
                     (13 13 (:META META-INTEGERP-CORRECT))
                     (11 10 (:REWRITE DEFAULT-PLUS-1))
                     (8 8
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (8 8 (:REWRITE NORMALIZE-ADDENDS))
                     (8 8 (:LINEAR RTL::FL-MONOTONE-LINEAR))
                     (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (6 2
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (6 2
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (4 4 (:LINEAR RTL::N<=FL-LINEAR))
                     (4 1 (:REWRITE RATIONALP-X))
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
                     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
                     (1 1 (:REWRITE REDUCE-RATIONALP-+))
                     (1 1 (:REWRITE REDUCE-RATIONALP-*))
                     (1 1 (:REWRITE RATIONALP-MINUS-X))
                     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::FL/INT-REWRITE
     (2326 22 (:REWRITE FLOOR-ZERO . 3))
     (2286 22 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (2135 471 (:REWRITE DEFAULT-TIMES-1))
     (1980 22 (:REWRITE FLOOR-ZERO . 4))
     (1966 22 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1927 22 (:REWRITE FLOOR-ZERO . 5))
     (1862 22 (:REWRITE CANCEL-FLOOR-+))
     (1261 471 (:REWRITE DEFAULT-TIMES-2))
     (1111 22 (:REWRITE FLOOR-=-X/Y . 2))
     (1063 22 (:REWRITE FLOOR-=-X/Y . 3))
     (867 24 (:REWRITE DEFAULT-FLOOR-RATIO))
     (790 22 (:REWRITE |(* (- x) y)|))
     (769 769
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (769 769
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (769 769
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (769 769
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (769 769
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (769 769
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (767 767 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (767 767 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (767 767
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (767 767
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (767 767
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (767 767
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (767 767
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (767 767
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (742 71
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (742 71 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (673 673
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (673 673
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (673 673
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (637 75 (:REWRITE THE-FLOOR-ABOVE))
     (601 72 (:REWRITE DEFAULT-LESS-THAN-1))
     (550 22 (:REWRITE |(integerp (- x))|))
     (427 19 (:REWRITE |(floor x 1)|))
     (398 8 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (348 8 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (237 31 (:REWRITE DEFAULT-PLUS-1))
     (234 31 (:REWRITE DEFAULT-PLUS-2))
     (214 72 (:REWRITE DEFAULT-LESS-THAN-2))
     (183 24 (:REWRITE DEFAULT-FLOOR-1))
     (182 11 (:REWRITE NORMALIZE-ADDENDS))
     (176 22 (:REWRITE FLOOR-ZERO . 2))
     (176 22 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (176 22 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (176 22
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (176 22 (:REWRITE FLOOR-CANCEL-*-CONST))
     (176 22 (:REWRITE DEFAULT-MINUS))
     (109 75 (:REWRITE THE-FLOOR-BELOW))
     (85 85
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (76 8
         (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (76 8
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (76 8
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (76 8
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (72 72
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (72 72
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (72 72
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (72 72
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (72 72 (:REWRITE INTEGERP-<-CONSTANT))
     (72 72 (:REWRITE CONSTANT-<-INTEGERP))
     (72 72
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (72 72
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (72 72
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (72 72
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (72 72 (:REWRITE |(< c (- x))|))
     (72 72
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (72 72
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (72 72
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (72 72
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (72 72 (:REWRITE |(< (/ x) (/ y))|))
     (72 72 (:REWRITE |(< (- x) c)|))
     (72 72 (:REWRITE |(< (- x) (- y))|))
     (71 71 (:REWRITE SIMPLIFY-SUMS-<))
     (71 71 (:REWRITE REDUCE-INTEGERP-+))
     (71 71 (:REWRITE INTEGERP-MINUS-X))
     (71 71 (:META META-INTEGERP-CORRECT))
     (54 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (54 2 (:REWRITE |(* (if a b c) x)|))
     (44 44 (:REWRITE |(< (/ x) 0)|))
     (44 44 (:REWRITE |(< (* x y) 0)|))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (33 33
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (29 21
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (24 24 (:REWRITE DEFAULT-FLOOR-2))
     (22 22
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (21 21 (:REWRITE |(floor x (- y))| . 2))
     (21 21 (:REWRITE |(floor x (- y))| . 1))
     (21 21
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (21 21 (:REWRITE |(floor (- x) y)| . 2))
     (21 21 (:REWRITE |(floor (- x) y)| . 1))
     (19 19
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (19 19 (:REWRITE DEFAULT-DIVIDE))
     (19 19
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (19 2
         (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (19 2
         (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (19 2
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (19 2
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (16 16
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< 0 (/ x))|))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (13 13 (:REWRITE |(- (* c x))|))
     (10 10
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (6 3 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3 (:REWRITE |(+ x (- x))|))
     (3 3 (:REWRITE |(+ 0 x)|))
     (2 2 (:REWRITE |(* 0 x)|))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE FLOOR-POSITIVE . 4))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 2))
     (1 1 (:REWRITE FLOOR-POSITIVE . 1))
     (1 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
     (1 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
     (1 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 5))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 4))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 3))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 2))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::FL/INT-REWRITE-ALT
     (4006 58 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (3720 58 (:REWRITE FLOOR-ZERO . 4))
     (3702 58 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (3458 58 (:REWRITE FLOOR-ZERO . 3))
     (3455 58 (:REWRITE FLOOR-ZERO . 5))
     (3186 58 (:REWRITE CANCEL-FLOOR-+))
     (2921 111 (:REWRITE THE-FLOOR-ABOVE))
     (2793 730 (:REWRITE DEFAULT-TIMES-1))
     (2488 730 (:REWRITE DEFAULT-TIMES-2))
     (1851 58 (:REWRITE FLOOR-=-X/Y . 2))
     (1775 64 (:REWRITE DEFAULT-FLOOR-RATIO))
     (1611 58 (:REWRITE FLOOR-=-X/Y . 3))
     (1509 404
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1374 58 (:REWRITE |(* (- x) y)|))
     (1304 1240
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1304 1240
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1302 1238
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1302 1238
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (1302 1238
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (1272 1240
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1272 1240
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1272 1240
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (1272 1240
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1270 1238
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1270 1238
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1270 1238
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1270 1238
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1270 1238
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (946 58 (:REWRITE |(integerp (- x))|))
     (941 119 (:REWRITE DEFAULT-PLUS-1))
     (926 119 (:REWRITE DEFAULT-PLUS-2))
     (892 37 (:REWRITE NORMALIZE-ADDENDS))
     (854 95 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (838 95
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (730 730
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (730 730
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (730 730
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (661 96 (:REWRITE DEFAULT-LESS-THAN-1))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (398 22 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (395 47 (:REWRITE |(floor x 1)|))
     (356 22 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (343 64 (:REWRITE DEFAULT-FLOOR-1))
     (296 58 (:REWRITE FLOOR-ZERO . 2))
     (296 58 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (296 58 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (296 58
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (296 58 (:REWRITE FLOOR-CANCEL-*-CONST))
     (296 58 (:REWRITE DEFAULT-MINUS))
     (290 96 (:REWRITE DEFAULT-LESS-THAN-2))
     (281 111 (:REWRITE THE-FLOOR-BELOW))
     (270 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (230 6 (:REWRITE |(* (if a b c) x)|))
     (107 107 (:REWRITE REDUCE-INTEGERP-+))
     (107 107 (:REWRITE INTEGERP-MINUS-X))
     (107 107 (:META META-INTEGERP-CORRECT))
     (101 101
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (96 96
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (96 96
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (96 96
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (96 96
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (96 96 (:REWRITE INTEGERP-<-CONSTANT))
     (96 96 (:REWRITE CONSTANT-<-INTEGERP))
     (96 96
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (96 96
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (96 96
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (96 96
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (96 96 (:REWRITE |(< c (- x))|))
     (96 96
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (96 96
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (96 96
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (96 96
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (96 96 (:REWRITE |(< (/ x) (/ y))|))
     (96 96 (:REWRITE |(< (- x) c)|))
     (96 96 (:REWRITE |(< (- x) (- y))|))
     (95 95 (:REWRITE SIMPLIFY-SUMS-<))
     (91 6
         (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (91 6
         (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (91 6
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (91 6
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (77 53
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (64 64 (:REWRITE DEFAULT-FLOOR-2))
     (63 63
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (63 63 (:REWRITE DEFAULT-DIVIDE))
     (60 60 (:REWRITE |(< (/ x) 0)|))
     (60 60 (:REWRITE |(< (* x y) 0)|))
     (59 59
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (59 59
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (58 58
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (53 53 (:REWRITE |(floor x (- y))| . 2))
     (53 53 (:REWRITE |(floor x (- y))| . 1))
     (53 53
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (53 53 (:REWRITE |(floor (- x) y)| . 2))
     (53 53 (:REWRITE |(floor (- x) y)| . 1))
     (47 47
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (30 15 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (29 29
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (18 18 (:REWRITE |(< 0 (/ x))|))
     (18 18 (:REWRITE |(< 0 (* x y))|))
     (17 17 (:REWRITE |(- (* c x))|))
     (15 15 (:REWRITE |(+ x (- x))|))
     (15 15 (:REWRITE |(+ 0 x)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (6 6
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (6 6 (:REWRITE |(* 0 x)|))
     (5 5 (:REWRITE FLOOR-POSITIVE . 4))
     (5 5 (:REWRITE FLOOR-POSITIVE . 3))
     (5 5 (:REWRITE FLOOR-POSITIVE . 2))
     (5 5 (:REWRITE FLOOR-POSITIVE . 1))
     (5 5 (:REWRITE FLOOR-NONPOSITIVE . 3))
     (5 5 (:REWRITE FLOOR-NONPOSITIVE . 2))
     (5 5 (:REWRITE FLOOR-NONPOSITIVE . 1))
     (5 5
        (:REWRITE |(floor (floor x y) z)| . 5))
     (5 5
        (:REWRITE |(floor (floor x y) z)| . 4))
     (5 5
        (:REWRITE |(floor (floor x y) z)| . 3))
     (5 5
        (:REWRITE |(floor (floor x y) z)| . 2))
     (4 1 (:REWRITE RATIONALP-X))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::FL*1/INT-REWRITE
     (112 16 (:REWRITE ACL2-NUMBERP-X))
     (108 24 (:REWRITE RATIONALP-X))
     (60 4 (:LINEAR RTL::FL-DEF))
     (42 9 (:REWRITE RTL::INTEGERP-FL))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:REWRITE INTEGERP-MINUS-X))
     (34 34 (:META META-INTEGERP-CORRECT))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24 (:META META-RATIONALP-CORRECT))
     (18 14 (:REWRITE DEFAULT-TIMES-1))
     (9 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (9 1
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (9 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (9 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
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
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR)))
(RTL::FL*1/INT-REWRITE-ALT
     (112 16 (:REWRITE ACL2-NUMBERP-X))
     (108 24 (:REWRITE RATIONALP-X))
     (60 4 (:LINEAR RTL::FL-DEF))
     (42 9 (:REWRITE RTL::INTEGERP-FL))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:REWRITE INTEGERP-MINUS-X))
     (34 34 (:META META-INTEGERP-CORRECT))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24 (:META META-RATIONALP-CORRECT))
     (9 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (9 1
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (9 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (9 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
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
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR)))
(RTL::FL-INT-DIV-RADIX
     (1896 47 (:REWRITE THE-FLOOR-BELOW))
     (1462 1462
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1462 1462
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1462 1462
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1462 1462
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (679 143 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (679 143
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (427 143 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (427 143 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (427 143 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (427 143
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (427 143
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (427 143
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (377 16 (:REWRITE DEFAULT-PLUS-1))
     (375 16 (:REWRITE DEFAULT-PLUS-2))
     (338 10 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (325 10 (:REWRITE CANCEL-FLOOR-+))
     (243 10
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (237 45
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (205 10 (:REWRITE FLOOR-=-X/Y . 3))
     (205 10 (:REWRITE FLOOR-=-X/Y . 2))
     (191 10 (:REWRITE FLOOR-ZERO . 3))
     (176 3 (:REWRITE FLOOR-=-X/Y . 4))
     (170 118 (:REWRITE DEFAULT-TIMES-2))
     (166 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (157 45
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (157 45
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (152 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (152 7
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (142 118 (:REWRITE DEFAULT-TIMES-1))
     (138 32 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (128 10 (:REWRITE |(integerp (- x))|))
     (126 44 (:REWRITE DEFAULT-LESS-THAN-2))
     (124 10 (:REWRITE FLOOR-ZERO . 5))
     (124 10 (:REWRITE FLOOR-ZERO . 4))
     (119 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (118 10 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (110 32 (:REWRITE SIMPLIFY-SUMS-<))
     (97 10 (:REWRITE |(* (- x) y)|))
     (95 10 (:REWRITE DEFAULT-FLOOR-RATIO))
     (70 22 (:REWRITE DEFAULT-MINUS))
     (66 66
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (59 3 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (56 56
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (56 56 (:REWRITE DEFAULT-DIVIDE))
     (55 3 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (50 5 (:REWRITE |(* (* x y) z)|))
     (43 43 (:REWRITE REDUCE-INTEGERP-+))
     (43 43 (:REWRITE INTEGERP-MINUS-X))
     (43 43 (:META META-INTEGERP-CORRECT))
     (39 39
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (39 39
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (39 39
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (35 35 (:REWRITE |(< (/ x) (/ y))|))
     (34 34
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (34 34 (:REWRITE INTEGERP-<-CONSTANT))
     (34 34 (:REWRITE CONSTANT-<-INTEGERP))
     (34 34
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (34 34
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (34 34
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (34 34
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (34 34 (:REWRITE |(< c (- x))|))
     (34 34
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (34 34
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (34 34
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (34 34
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (34 34 (:REWRITE |(< (- x) c)|))
     (34 10 (:REWRITE FLOOR-ZERO . 2))
     (34 10 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (34 10 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (34 10
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (34 10 (:REWRITE FLOOR-CANCEL-*-CONST))
     (30 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (30 10
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (16 1 (:REWRITE |(floor x 1)|))
     (14 10 (:REWRITE DEFAULT-FLOOR-1))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (11 3
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE DEFAULT-FLOOR-2))
     (10 10 (:REWRITE |(floor x (- y))| . 2))
     (10 10 (:REWRITE |(floor x (- y))| . 1))
     (10 10
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (10 10 (:REWRITE |(floor (- x) y)| . 2))
     (10 10 (:REWRITE |(floor (- x) y)| . 1))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (10 10 (:REWRITE |(- (* c x))|))
     (9 9
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5 5
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (1 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(RTL::FL-HALF-INT)
(RTL::FL-MINUS (18 9 (:REWRITE DEFAULT-PLUS-2))
               (14 9 (:REWRITE DEFAULT-PLUS-1))
               (13 9 (:REWRITE RTL::INTEGERP-FL))
               (8 8 (:LINEAR RTL::FL-MONOTONE-LINEAR))
               (6 6
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (6 2
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (4 4 (:LINEAR RTL::N<=FL-LINEAR))
               (4 3 (:REWRITE DEFAULT-MINUS))
               (4 1 (:REWRITE RATIONALP-X))
               (4 1 (:REWRITE |(integerp (- x))|))
               (3 3 (:REWRITE REDUCE-INTEGERP-+))
               (3 3 (:REWRITE INTEGERP-MINUS-X))
               (3 3 (:META META-INTEGERP-CORRECT))
               (3 2 (:REWRITE |(equal (- x) (- y))|))
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
               (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
               (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
               (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (1 1 (:REWRITE REDUCE-RATIONALP-+))
               (1 1 (:REWRITE REDUCE-RATIONALP-*))
               (1 1 (:REWRITE RATIONALP-MINUS-X))
               (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::MINUS-FL)
(RTL::FL-M-N
     (2882 24 (:REWRITE FLOOR-ZERO . 3))
     (2354 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2354 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2354 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2294 142 (:REWRITE DEFAULT-PLUS-2))
     (1622 24 (:REWRITE FLOOR-ZERO . 4))
     (1597 24 (:REWRITE FLOOR-ZERO . 5))
     (1546 181 (:REWRITE |(< (- x) c)|))
     (1451 24 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1285 785 (:REWRITE DEFAULT-TIMES-1))
     (1239 155 (:REWRITE DEFAULT-MINUS))
     (1108 161
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1068 24 (:REWRITE CANCEL-FLOOR-+))
     (897 785 (:REWRITE DEFAULT-TIMES-2))
     (778 26 (:REWRITE FLOOR-=-X/Y . 2))
     (693 26 (:REWRITE FLOOR-=-X/Y . 3))
     (564 26 (:REWRITE DEFAULT-FLOOR-RATIO))
     (547 191 (:REWRITE DEFAULT-LESS-THAN-1))
     (531 186 (:REWRITE |(< c (- x))|))
     (327 191 (:REWRITE DEFAULT-LESS-THAN-2))
     (327 159 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (327 159
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (327 159
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (327 159
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (327 159
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (297 142 (:REWRITE DEFAULT-PLUS-1))
     (266 186 (:REWRITE |(< (- x) (- y))|))
     (258 102 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (258 102
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (255 19 (:REWRITE |(floor x 1)|))
     (244 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (243 159 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (243 159 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (243 159
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (228 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (217 89 (:REWRITE REDUCE-INTEGERP-+))
     (191 191 (:REWRITE THE-FLOOR-BELOW))
     (191 191 (:REWRITE THE-FLOOR-ABOVE))
     (191 191
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (191 191
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (186 186
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (186 186
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (186 186
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (186 186
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (186 186
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (186 186
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (186 186
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (186 186
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (186 186 (:REWRITE |(< (/ x) (/ y))|))
     (179 143 (:REWRITE SIMPLIFY-SUMS-<))
     (174 174
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (161 161
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (161 161 (:REWRITE INTEGERP-<-CONSTANT))
     (161 161 (:REWRITE CONSTANT-<-INTEGERP))
     (135 3 (:REWRITE MOD-X-Y-=-X . 4))
     (135 3 (:REWRITE MOD-X-Y-=-X . 3))
     (132 132 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (122 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (108 3 (:REWRITE CANCEL-MOD-+))
     (105 89 (:REWRITE INTEGERP-MINUS-X))
     (102 102 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (102 102 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (102 102
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (90 90 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (90 90 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (89 89 (:META META-INTEGERP-CORRECT))
     (83 83 (:REWRITE |(< (/ x) 0)|))
     (83 83 (:REWRITE |(< (* x y) 0)|))
     (83 3 (:REWRITE MOD-ZERO . 4))
     (82 26 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (80 24 (:REWRITE FLOOR-ZERO . 2))
     (80 24 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (80 24
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (80 24 (:REWRITE FLOOR-CANCEL-*-CONST))
     (74 26 (:REWRITE DEFAULT-FLOOR-1))
     (73 13 (:REWRITE INTEGERP-/))
     (65 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (65 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (64 64
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (63 63
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (63 7 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (61 61
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (61 61
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (61 61 (:REWRITE |(- (* c x))|))
     (54 3 (:REWRITE MOD-ZERO . 3))
     (52 52 (:REWRITE |(< 0 (/ x))|))
     (52 52 (:REWRITE |(< 0 (* x y))|))
     (48 10
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (48 4 (:REWRITE DEFAULT-MOD-RATIO))
     (46 46
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (46 46
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (46 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (43 43
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (43 43
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (41 41 (:REWRITE DEFAULT-DIVIDE))
     (35 7 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (29 29 (:REWRITE |(* x (- y))|))
     (27 27
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (27 27
         (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (27 19
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (26 26 (:REWRITE DEFAULT-FLOOR-2))
     (24 24
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (24 24 (:REWRITE |(floor x (- y))| . 2))
     (24 24 (:REWRITE |(floor x (- y))| . 1))
     (24 24 (:REWRITE |(floor (- x) y)| . 2))
     (22 2 (:REWRITE |(mod x 1)|))
     (19 19
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (19 19
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (15 3 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 3
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (13 13
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (13 13
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (13 13 (:REWRITE |(equal (/ x) (/ y))|))
     (13 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (12 12
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (12 12
         (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (12 12
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (12 12
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (12 12
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (12 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (12 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (11 11 (:REWRITE |(< (+ c/d x) y)|))
     (11 3
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (11 3 (:REWRITE MOD-CANCEL-*-CONST))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (9 1
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (8 4 (:REWRITE DEFAULT-MOD-1))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (7 3
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (6 1 (:REWRITE |(floor (+ x r) i)|))
     (5 5
        (:REWRITE |(<= (* x (/ y)) -1) with (< y 0)|))
     (5 5
        (:REWRITE |(<= (* x (/ y)) -1) with (< 0 y)|))
     (5 5
        (:REWRITE |(< -1 (* x (/ y))) with (< y 0)|))
     (5 5
        (:REWRITE |(< -1 (* x (/ y))) with (< 0 y)|))
     (5 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (5 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(mod x (- y))| . 3))
     (3 3 (:REWRITE |(mod x (- y))| . 2))
     (3 3 (:REWRITE |(mod x (- y))| . 1))
     (3 3
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(mod (- x) y)| . 3))
     (3 3 (:REWRITE |(mod (- x) y)| . 2))
     (3 3 (:REWRITE |(mod (- x) y)| . 1))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (1 1
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (1 1
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (1 1
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(RTL::CG)
(RTL::CG-DEFAULT (44 11 (:REWRITE RATIONALP-X))
                 (33 6 (:REWRITE RTL::INTEGERP-FL))
                 (31 31 (:REWRITE ACL2-NUMBERP-X))
                 (20 12 (:REWRITE INTEGERP-MINUS-X))
                 (19 11 (:REWRITE RATIONALP-MINUS-X))
                 (16 8 (:REWRITE |(integerp (- x))|))
                 (12 12 (:REWRITE REDUCE-INTEGERP-+))
                 (12 12 (:META META-INTEGERP-CORRECT))
                 (12 8 (:REWRITE |(rationalp (- x))|))
                 (11 11 (:REWRITE REDUCE-RATIONALP-+))
                 (11 11 (:REWRITE REDUCE-RATIONALP-*))
                 (11 11 (:META META-RATIONALP-CORRECT))
                 (8 8 (:LINEAR RTL::FL-MONOTONE-LINEAR))
                 (4 4 (:LINEAR RTL::N<=FL-LINEAR))
                 (4 2 (:REWRITE DEFAULT-PLUS-2))
                 (3 2 (:REWRITE |(equal (- x) (- y))|))
                 (2 2
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (2 2
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                 (2 2
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (2 2 (:REWRITE NORMALIZE-ADDENDS))
                 (2 2 (:REWRITE DEFAULT-PLUS-1))
                 (2 2 (:REWRITE |(equal c (/ x))|))
                 (2 2 (:REWRITE |(equal c (- x))|))
                 (2 2 (:REWRITE |(equal (/ x) c)|))
                 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
                 (2 1
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (2 1
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (1 1
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (1 1
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE)))
(RTL::CG-DEF
     (25 5 (:REWRITE RTL::INTEGERP-FL))
     (20 5 (:REWRITE |(integerp (- x))|))
     (15 9 (:REWRITE DEFAULT-PLUS-2))
     (14 9 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 4 (:REWRITE DEFAULT-MINUS))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 3 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (4 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (3 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR))
     (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CG-UNIQUE (2 2
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (2 2 (:REWRITE NORMALIZE-ADDENDS))
                (2 2 (:REWRITE DEFAULT-PLUS-2))
                (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::CG-INTEGERP (4 1 (:REWRITE RATIONALP-X))
                  (2 2 (:REWRITE REDUCE-INTEGERP-+))
                  (2 2
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (2 2 (:REWRITE NORMALIZE-ADDENDS))
                  (2 2 (:REWRITE INTEGERP-MINUS-X))
                  (2 2 (:REWRITE DEFAULT-PLUS-2))
                  (2 2 (:REWRITE DEFAULT-PLUS-1))
                  (2 2 (:META META-INTEGERP-CORRECT))
                  (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (2 1
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (2 1
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (1 1 (:REWRITE REDUCE-RATIONALP-+))
                  (1 1 (:REWRITE REDUCE-RATIONALP-*))
                  (1 1
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (1 1
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE RATIONALP-MINUS-X))
                  (1 1
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (1 1 (:REWRITE |(equal c (/ x))|))
                  (1 1 (:REWRITE |(equal c (- x))|))
                  (1 1 (:REWRITE |(equal (/ x) c)|))
                  (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                  (1 1 (:REWRITE |(equal (- x) c)|))
                  (1 1 (:REWRITE |(equal (- x) (- y))|))
                  (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CG-MONOTONE-LINEAR (2 2
                            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                         (2 2 (:REWRITE NORMALIZE-ADDENDS))
                         (2 2 (:REWRITE DEFAULT-PLUS-2))
                         (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::N>=CG-LINEAR
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(RTL::CG+INT-REWRITE
     (240 8 (:LINEAR RTL::CG-MONOTONE-LINEAR))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:LINEAR RTL::N>=CG-LINEAR))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(+ c (+ d x))|)))
(RTL::CG/INT-REWRITE
     (151 7 (:REWRITE RTL::INTEGERP-FL))
     (96 6 (:REWRITE |(integerp (- x))|))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (29 8 (:REWRITE DEFAULT-MINUS))
     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (10 8 (:REWRITE DEFAULT-TIMES-1))
     (9 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE DEFAULT-DIVIDE))
     (3 3 (:REWRITE |(- (* c x))|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
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
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CG/INT-REWRITE-ALT
     (151 7 (:REWRITE RTL::INTEGERP-FL))
     (96 6 (:REWRITE |(integerp (- x))|))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (29 8 (:REWRITE DEFAULT-MINUS))
     (9 7 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE DEFAULT-DIVIDE))
     (3 3 (:REWRITE |(- (* c x))|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
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
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::FL-CG (12 4 (:LINEAR RTL::CG-MONOTONE-LINEAR))
            (8 5 (:REWRITE DEFAULT-PLUS-2))
            (5 5
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (5 5 (:REWRITE NORMALIZE-ADDENDS))
            (5 5 (:REWRITE DEFAULT-PLUS-1))
            (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
            (4 1 (:REWRITE RATIONALP-X))
            (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (3 1
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (3 1
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (2 2 (:REWRITE REDUCE-INTEGERP-+))
            (2 2 (:REWRITE INTEGERP-MINUS-X))
            (2 2 (:META META-INTEGERP-CORRECT))
            (2 2 (:LINEAR RTL::N>=CG-LINEAR))
            (2 2 (:LINEAR RTL::N<=FL-LINEAR))
            (1 1 (:REWRITE REDUCE-RATIONALP-+))
            (1 1 (:REWRITE REDUCE-RATIONALP-*))
            (1 1
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
            (1 1
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
            (1 1 (:REWRITE RATIONALP-MINUS-X))
            (1 1
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
            (1 1 (:REWRITE |(equal c (/ x))|))
            (1 1 (:REWRITE |(equal c (- x))|))
            (1 1 (:REWRITE |(equal (/ x) c)|))
            (1 1 (:REWRITE |(equal (/ x) (/ y))|))
            (1 1 (:REWRITE |(equal (- x) c)|))
            (1 1 (:REWRITE |(equal (- x) (- y))|))
            (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
            (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::MOD-DEF
     (24400 57 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (17890 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (17706 52 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (13340 29
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (9111 78
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6858 82
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2926 321 (:REWRITE DEFAULT-PLUS-2))
     (2275 54 (:REWRITE FLOOR-ZERO . 3))
     (1680 54 (:REWRITE FLOOR-ZERO . 5))
     (1680 54 (:REWRITE FLOOR-ZERO . 4))
     (1626 54 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1625 54 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1591 54 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (1591 54 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (1275 321 (:REWRITE DEFAULT-PLUS-1))
     (1100 563 (:REWRITE DEFAULT-TIMES-2))
     (1033 54 (:REWRITE CANCEL-FLOOR-+))
     (925 54 (:REWRITE FLOOR-=-X/Y . 3))
     (925 54 (:REWRITE FLOOR-=-X/Y . 2))
     (855 839
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (855 839
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (855 839
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (855 839
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (855 839
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (855 839
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (843 827 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (843 827 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (843 827
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (843 827
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (843 827
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (843 827
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (843 827
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (843 827
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (715 715
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (715 715
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (715 715
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (715 715
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (571 19 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (442 26 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (442 26 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (432 54 (:REWRITE |(integerp (- x))|))
     (421 421
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (397 397
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (382 382 (:REWRITE THE-FLOOR-BELOW))
     (382 382 (:REWRITE THE-FLOOR-ABOVE))
     (382 382 (:REWRITE SIMPLIFY-SUMS-<))
     (382 382
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (382 382
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (382 382
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (382 382
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (382 382
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (382 382
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (382 382 (:REWRITE INTEGERP-<-CONSTANT))
     (382 382 (:REWRITE DEFAULT-LESS-THAN-2))
     (382 382 (:REWRITE DEFAULT-LESS-THAN-1))
     (382 382 (:REWRITE CONSTANT-<-INTEGERP))
     (382 382
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (382 382
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (382 382
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (382 382
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (382 382 (:REWRITE |(< c (- x))|))
     (382 382
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (382 382
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (382 382
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (382 382
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (382 382 (:REWRITE |(< (/ x) (/ y))|))
     (382 382 (:REWRITE |(< (- x) c)|))
     (382 382 (:REWRITE |(< (- x) (- y))|))
     (333 54 (:REWRITE |(* (- x) y)|))
     (324 9 (:REWRITE FLOOR-=-X/Y . 4))
     (242 242 (:REWRITE REDUCE-INTEGERP-+))
     (242 242 (:REWRITE INTEGERP-MINUS-X))
     (242 242 (:META META-INTEGERP-CORRECT))
     (238 22 (:REWRITE REDUCE-RATIONALP-*))
     (231 78 (:REWRITE |(equal (- x) (- y))|))
     (223 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (205 205
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (205 205
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (205 205 (:REWRITE |(< (/ x) 0)|))
     (205 205 (:REWRITE |(< (* x y) 0)|))
     (192 4 (:REWRITE |(* x (+ y z))|))
     (186 38 (:REWRITE |(+ c (+ d x))|))
     (180 26 (:REWRITE RATIONALP-X))
     (169 64 (:REWRITE DEFAULT-MINUS))
     (163 163
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (163 163
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (163 163 (:REWRITE |(< 0 (/ x))|))
     (163 163 (:REWRITE |(< 0 (* x y))|))
     (152 152 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (140 44 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (108 44 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (96 8 (:DEFINITION RFIX))
     (90 90
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (90 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (90 5 (:REWRITE |(* a (/ a) b)|))
     (82 82
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (78 78
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (78 78 (:REWRITE |(equal c (/ x))|))
     (78 78 (:REWRITE |(equal c (- x))|))
     (78 78 (:REWRITE |(equal (/ x) c)|))
     (78 78 (:REWRITE |(equal (/ x) (/ y))|))
     (78 78 (:REWRITE |(equal (- x) c)|))
     (70 5 (:REWRITE |(equal (* x (/ y)) 1)|))
     (66 58 (:REWRITE DEFAULT-FLOOR-1))
     (58 58 (:REWRITE DEFAULT-FLOOR-2))
     (56 8 (:REWRITE ACL2-NUMBERP-X))
     (56 4 (:REWRITE |(equal (* x (/ y)) -1)|))
     (55 55 (:REWRITE |(- (* c x))|))
     (54 54 (:REWRITE FLOOR-ZERO . 2))
     (54 54
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (54 54
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (54 54 (:REWRITE FLOOR-CANCEL-*-CONST))
     (54 54 (:REWRITE |(floor x (- y))| . 2))
     (54 54 (:REWRITE |(floor x (- y))| . 1))
     (54 54
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (54 54
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (54 54 (:REWRITE |(floor (- x) y)| . 2))
     (54 54 (:REWRITE |(floor (- x) y)| . 1))
     (53 53
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (44 44 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (44 44 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (44 44 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (44 44
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (44 44
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (44 44 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (44 44 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (44 44
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (44 44
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (44 44 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (44 44 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (43 43
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (43 43
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (36 4 (:REWRITE RATIONALP-/))
     (31 31 (:REWRITE |(equal (+ (- c) x) y)|))
     (31 1 (:REWRITE MOD-X-Y-=-X . 4))
     (31 1 (:REWRITE MOD-X-Y-=-X . 3))
     (30 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (30 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (30 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (30 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (22 22 (:REWRITE REDUCE-RATIONALP-+))
     (22 22 (:REWRITE RATIONALP-MINUS-X))
     (22 22 (:META META-RATIONALP-CORRECT))
     (21 5
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (20 4 (:LINEAR MOD-BOUNDS-1))
     (17 1 (:REWRITE MOD-ZERO . 3))
     (15 15 (:REWRITE FOLD-CONSTS-IN-+))
     (14 14
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (14 14
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (14 1 (:REWRITE MOD-ZERO . 4))
     (14 1 (:REWRITE MOD-X-Y-=-X . 2))
     (14 1 (:REWRITE CANCEL-MOD-+))
     (14 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (14 1
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (12 1 (:REWRITE |(floor x 1)|))
     (10 2 (:LINEAR MOD-BOUNDS-3))
     (9 9
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5 5 (:REWRITE FLOOR-X-Y-=-1 . 1))
     (4 4 (:REWRITE INTEGERP-/))
     (4 4 (:REWRITE FLOOR-X-Y-=--1 . 1))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE |(equal x (/ y))|))
     (3 3 (:REWRITE DEFAULT-MOD-1))
     (1 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE MOD-CANCEL-*-CONST))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (1 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|)))
(RTL::MOD-0 (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
            (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
            (24 24
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
            (24 24
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
            (24 24
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
            (24 24
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
            (23 23 (:TYPE-PRESCRIPTION RATIONALP-MOD))
            (23 23 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
            (23 23 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
            (23 23 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
            (23 23 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
            (23 23 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
            (20 4 (:LINEAR MOD-BOUNDS-2))
            (20 4 (:LINEAR MOD-BOUNDS-1))
            (19 3 (:REWRITE ACL2-NUMBERP-X))
            (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (10 2 (:LINEAR MOD-BOUNDS-3))
            (8 2 (:REWRITE RATIONALP-X))
            (7 1 (:REWRITE DEFAULT-MOD-RATIO))
            (4 1 (:REWRITE |(* y x)|))
            (2 2 (:REWRITE REDUCE-RATIONALP-+))
            (2 2 (:REWRITE REDUCE-RATIONALP-*))
            (2 2 (:REWRITE REDUCE-INTEGERP-+))
            (2 2 (:REWRITE RATIONALP-MINUS-X))
            (2 2 (:REWRITE INTEGERP-MINUS-X))
            (2 2 (:REWRITE DEFAULT-TIMES-2))
            (2 2 (:REWRITE DEFAULT-TIMES-1))
            (2 2 (:REWRITE DEFAULT-MOD-2))
            (2 2 (:META META-RATIONALP-CORRECT))
            (2 2 (:META META-INTEGERP-CORRECT))
            (1 1 (:REWRITE |(* 0 x)|)))
(RTL::RATIONALP-MOD (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                    (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                    (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                    (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                    (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                    (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                    (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                    (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                    (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                    (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                    (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-1)))
(RTL::INTEGERP-MOD (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (7 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (7 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (7 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                   (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                   (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                   (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                   (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                   (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD)))
(RTL::NATP-MOD
     (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (112 24 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (105 105
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (105 105
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (105 105
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (105 105
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (104 24
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (104 24
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (35 1 (:REWRITE MOD-X-Y-=-X . 4))
     (34 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (34 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (30 1 (:REWRITE MOD-X-Y-=-X . 3))
     (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (24 24
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (24 24 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (24 24 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (24 24
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (21 1 (:REWRITE MOD-ZERO . 3))
     (18 1 (:REWRITE MOD-ZERO . 4))
     (18 1 (:REWRITE MOD-X-Y-=-X . 2))
     (18 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (18 1
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (14 1 (:REWRITE CANCEL-MOD-+))
     (10 1 (:REWRITE DEFAULT-MOD-RATIO))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (5 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (5 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE MOD-CANCEL-*-CONST))
     (5 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (5 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE DEFAULT-TIMES-2))
     (2 2 (:REWRITE DEFAULT-TIMES-1))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|)))
(RTL::NATP-MOD-2 (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                 (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (2 1 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
                 (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                 (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                 (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                 (1 1
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)))
(RTL::MOD-BND-1
     (260 52 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (247 247
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (247 247
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (247 247
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (247 247
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (236 52 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (156 4 (:REWRITE CANCEL-MOD-+))
     (140 4 (:REWRITE MOD-X-Y-=-X . 4))
     (140 4 (:REWRITE MOD-X-Y-=-X . 3))
     (136 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (124 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (108 52
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (108 52
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (104 52 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (90 10 (:REWRITE ACL2-NUMBERP-X))
     (86 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (84 4 (:REWRITE MOD-ZERO . 3))
     (72 4 (:REWRITE MOD-ZERO . 4))
     (64 4 (:REWRITE |(integerp (- x))|))
     (62 2 (:LINEAR MOD-BOUNDS-3))
     (52 52 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (52 52 (:TYPE-PRESCRIPTION NATP))
     (52 52 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (52 52 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (52 52
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (52 52 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (52 52
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (52 52 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (52 52 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (52 52
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (52 19 (:REWRITE SIMPLIFY-SUMS-<))
     (52 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (52 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (40 10 (:REWRITE RATIONALP-X))
     (40 4 (:REWRITE DEFAULT-MOD-RATIO))
     (40 4 (:REWRITE |(* (- x) y)|))
     (39 19 (:REWRITE DEFAULT-TIMES-1))
     (38 38 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20 (:META META-INTEGERP-CORRECT))
     (20 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (20 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (20 4 (:REWRITE MOD-X-Y-=-X . 2))
     (20 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (20 4 (:REWRITE MOD-CANCEL-*-CONST))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (20 4
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (20 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (20 4
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (20 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (19 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (19 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19 (:REWRITE INTEGERP-<-CONSTANT))
     (19 19 (:REWRITE DEFAULT-TIMES-2))
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
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (14 14
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (14 14 (:REWRITE DEFAULT-DIVIDE))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10 (:META META-RATIONALP-CORRECT))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 7 (:REWRITE DEFAULT-MOD-2))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(- (* c x))|)))
(RTL::MOD-BY-1 (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
               (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
               (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
               (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
               (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
               (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
               (1 1
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)))
(RTL::MOD-BND-2
     (2094 81 (:REWRITE THE-FLOOR-BELOW))
     (1141 2 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (779 779
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (779 779
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (779 779
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (779 779
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (435 24 (:REWRITE DEFAULT-PLUS-2))
     (320 24 (:REWRITE DEFAULT-PLUS-1))
     (302 5 (:REWRITE FLOOR-ZERO . 3))
     (297 85 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (297 85
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (297 85
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (257 36 (:REWRITE RATIONALP-X))
     (229 82 (:REWRITE DEFAULT-TIMES-2))
     (229 78 (:REWRITE DEFAULT-LESS-THAN-1))
     (225 77
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (225 77
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (197 85 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (197 85 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (197 85 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (197 85
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (197 85
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (197 85
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (197 85
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (197 85
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (162 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (162 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (162 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (162 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (157 77
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (157 77
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (155 5 (:REWRITE CANCEL-FLOOR-+))
     (140 35
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (140 35
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (136 16 (:REWRITE ACL2-NUMBERP-X))
     (132 2 (:LINEAR MOD-BOUNDS-2))
     (132 2 (:LINEAR MOD-BOUNDS-1))
     (129 53 (:REWRITE DEFAULT-DIVIDE))
     (116 82 (:REWRITE DEFAULT-TIMES-1))
     (97 5 (:REWRITE FLOOR-=-X/Y . 3))
     (97 5 (:REWRITE FLOOR-=-X/Y . 2))
     (93 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (92 5 (:REWRITE FLOOR-ZERO . 4))
     (77 5 (:REWRITE FLOOR-ZERO . 5))
     (70 35 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (69 69
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (69 69
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (69 69
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (67 67
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (67 67 (:REWRITE INTEGERP-<-CONSTANT))
     (67 67 (:REWRITE CONSTANT-<-INTEGERP))
     (67 67
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (67 67
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (67 67
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (67 67
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (67 67 (:REWRITE |(< c (- x))|))
     (67 67
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (67 67
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (67 67
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (67 67
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (67 67 (:REWRITE |(< (/ x) (/ y))|))
     (67 67 (:REWRITE |(< (- x) c)|))
     (67 67 (:REWRITE |(< (- x) (- y))|))
     (64 5 (:REWRITE |(integerp (- x))|))
     (64 4 (:REWRITE |(equal (if a b c) x)|))
     (62 2 (:REWRITE MOD-X-Y-=-X . 4))
     (60 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (60 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (60 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (60 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (60 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (60 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (57 2 (:REWRITE FLOOR-=-X/Y . 4))
     (56 5 (:REWRITE FLOOR-ZERO . 2))
     (55 55 (:REWRITE REDUCE-INTEGERP-+))
     (55 55 (:REWRITE INTEGERP-MINUS-X))
     (55 55 (:META META-INTEGERP-CORRECT))
     (53 7 (:REWRITE DEFAULT-MINUS))
     (52 2 (:REWRITE MOD-X-Y-=-X . 3))
     (49 49
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (47 47
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (42 5 (:REWRITE DEFAULT-FLOOR-RATIO))
     (42 5 (:REWRITE |(* (- x) y)|))
     (40 4 (:REWRITE |(* x (if a b c))|))
     (37 37
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (37 37
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (37 37 (:REWRITE |(equal c (/ x))|))
     (37 37 (:REWRITE |(equal (/ x) (/ y))|))
     (37 37 (:REWRITE |(equal (- x) (- y))|))
     (35 35 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (35 35 (:TYPE-PRESCRIPTION NATP))
     (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (35 35
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (35 35
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (35 35
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (35 35
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (35 35
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (35 35
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (35 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (35 35
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (35 35 (:REWRITE |(equal c (- x))|))
     (35 35 (:REWRITE |(equal (- x) c)|))
     (34 34 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (34 34 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (34 34 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (34 34 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (34 34 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (34 2 (:REWRITE MOD-ZERO . 3))
     (31 31 (:REWRITE RATIONALP-MINUS-X))
     (30 30 (:REWRITE REDUCE-RATIONALP-+))
     (30 30 (:REWRITE |(< 0 (* x y))|))
     (30 30 (:META META-RATIONALP-CORRECT))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (29 29 (:REWRITE |(< 0 (/ x))|))
     (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (28 2 (:REWRITE MOD-ZERO . 4))
     (28 2 (:REWRITE MOD-X-Y-=-X . 2))
     (28 2 (:REWRITE CANCEL-MOD-+))
     (28 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (28 2
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (25 25 (:REWRITE |(< (* x y) 0)|))
     (25 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (21 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (13 5
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (13 5 (:REWRITE FLOOR-CANCEL-*-CONST))
     (13 5
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (13 5
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (10 1 (:LINEAR MOD-BOUNDS-3))
     (9 5
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (9 5
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (9 5
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (7 7 (:REWRITE |(- (* c x))|))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6 (:REWRITE |(not (equal x (/ y)))|))
     (6 6 (:REWRITE |(equal x (/ y))|))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE INTEGERP-/))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE DEFAULT-FLOOR-1))
     (5 5 (:REWRITE |(floor x (- y))| . 2))
     (5 5 (:REWRITE |(floor x (- y))| . 1))
     (5 5 (:REWRITE |(floor (- x) y)| . 2))
     (5 5 (:REWRITE |(floor (- x) y)| . 1))
     (5 5
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (5 1
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (2 2
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (2 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE MOD-CANCEL-*-CONST))
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
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1 1 (:REWRITE FLOOR-POSITIVE . 4))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 2))
     (1 1 (:REWRITE |(equal (* x y) 0)|))
     (1 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (1 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(RTL::MOD-DOES-NOTHING
     (684 2 (:LINEAR RTL::MOD-BND-2))
     (647 57 (:REWRITE REDUCE-RATIONALP-*))
     (494 67 (:REWRITE RATIONALP-X))
     (264 4 (:LINEAR MOD-BOUNDS-2))
     (264 4 (:LINEAR MOD-BOUNDS-1))
     (252 28 (:REWRITE ACL2-NUMBERP-X))
     (188 36 (:REWRITE DEFAULT-DIVIDE))
     (160 20 (:DEFINITION RFIX))
     (160 10 (:REWRITE |(equal (if a b c) x)|))
     (155 5 (:REWRITE MOD-X-Y-=-X . 4))
     (150 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (150 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (145 29 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (142 142
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (142 142
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (142 142
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (142 142
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (90 10 (:REWRITE RATIONALP-/))
     (85 5 (:REWRITE MOD-ZERO . 3))
     (80 8 (:REWRITE |(* x (if a b c))|))
     (72 72 (:REWRITE REDUCE-INTEGERP-+))
     (72 72 (:REWRITE INTEGERP-MINUS-X))
     (72 72 (:META META-INTEGERP-CORRECT))
     (70 5 (:REWRITE MOD-ZERO . 4))
     (58 29 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (57 57 (:REWRITE REDUCE-RATIONALP-+))
     (57 57 (:REWRITE RATIONALP-MINUS-X))
     (57 57 (:META META-RATIONALP-CORRECT))
     (52 52 (:REWRITE DEFAULT-TIMES-2))
     (52 52 (:REWRITE DEFAULT-TIMES-1))
     (49 29 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (35 35
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (35 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (35 35
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (35 35
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (35 35
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (35 35
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (35 35 (:REWRITE |(equal c (/ x))|))
     (35 35 (:REWRITE |(equal c (- x))|))
     (35 35 (:REWRITE |(equal (/ x) c)|))
     (35 35 (:REWRITE |(equal (/ x) (/ y))|))
     (35 35 (:REWRITE |(equal (- x) c)|))
     (35 35 (:REWRITE |(equal (- x) (- y))|))
     (34 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (34 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (32 8 (:REWRITE |(* y x)|))
     (29 29 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (29 29 (:TYPE-PRESCRIPTION NATP))
     (29 29 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (29 29 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (29 29
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (29 29
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (29 29 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (29 29 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (29 29
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (29 29
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (29 29 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (29 29 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (29 29
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (28 28
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (20 20
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (20 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (20 20 (:REWRITE INTEGERP-<-CONSTANT))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (20 2 (:LINEAR MOD-BOUNDS-3))
     (19 19 (:REWRITE SIMPLIFY-SUMS-<))
     (19 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE INTEGERP-/))
     (10 10 (:REWRITE DEFAULT-MOD-1))
     (10 10 (:REWRITE |(not (equal x (/ y)))|))
     (10 10 (:REWRITE |(equal x (/ y))|))
     (8 8 (:REWRITE |(* 0 x)|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< 0 (/ x))|))
     (7 7 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD)))
(RTL::MOD-0-FL
     (2356 2356
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2356 2356
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2356 2356
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2352 274
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2080 76 (:LINEAR MOD-BOUNDS-2))
     (1771 40 (:REWRITE FLOOR-ZERO . 3))
     (1540 28 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (1318 40 (:REWRITE FLOOR-ZERO . 5))
     (1318 40 (:REWRITE FLOOR-ZERO . 4))
     (1261 199 (:REWRITE RATIONALP-X))
     (1227 178 (:REWRITE REDUCE-RATIONALP-*))
     (1178 38 (:LINEAR RTL::MOD-BND-2))
     (1088 864 (:REWRITE DEFAULT-TIMES-1))
     (1075 40 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1059 40 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1032 41 (:REWRITE RTL::MOD-DOES-NOTHING))
     (965 35 (:REWRITE MOD-X-Y-=-X . 4))
     (965 35 (:REWRITE MOD-X-Y-=-X . 3))
     (952 816
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (952 816
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (952 816
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (952 816
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (952 816
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (952 816
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (934 35 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (928 35 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (918 782 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (918 782 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (918 782
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (918 782
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (918 782
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (918 782
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (918 782
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (918 782
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (851 40 (:REWRITE CANCEL-FLOOR-+))
     (823 40 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (817 40 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (763 40 (:REWRITE FLOOR-=-X/Y . 3))
     (763 40 (:REWRITE FLOOR-=-X/Y . 2))
     (731 35 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (731 35 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (716 274
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (711 641 (:REWRITE DEFAULT-LESS-THAN-2))
     (688 246 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (641 641 (:REWRITE THE-FLOOR-BELOW))
     (641 641 (:REWRITE THE-FLOOR-ABOVE))
     (640 640 (:REWRITE SIMPLIFY-SUMS-<))
     (640 640
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (640 640
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (640 640
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (640 640
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (640 640
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (640 640
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (640 640 (:REWRITE INTEGERP-<-CONSTANT))
     (640 640 (:REWRITE DEFAULT-LESS-THAN-1))
     (640 640 (:REWRITE CONSTANT-<-INTEGERP))
     (640 640
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (640 640
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (640 640
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (640 640
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (640 640 (:REWRITE |(< c (- x))|))
     (640 640
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (640 640
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (640 640
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (640 640
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (640 640 (:REWRITE |(< (/ x) (/ y))|))
     (640 640 (:REWRITE |(< (- x) c)|))
     (640 640 (:REWRITE |(< (- x) (- y))|))
     (598 38 (:LINEAR MOD-BOUNDS-3))
     (560 560
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (560 560 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (560 560 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (559 559
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (559 559
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (559 559
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (558 558 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (558 558 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (553 553 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (538 35 (:REWRITE CANCEL-MOD-+))
     (532 28 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (528 66 (:DEFINITION RFIX))
     (527 35 (:REWRITE MOD-ZERO . 3))
     (480 60 (:REWRITE |(integerp (- x))|))
     (477 60 (:REWRITE |(* (- x) y)|))
     (472 28 (:REWRITE MOD-ZERO . 1))
     (448 448 (:REWRITE REDUCE-INTEGERP-+))
     (448 448 (:REWRITE INTEGERP-MINUS-X))
     (448 448 (:META META-INTEGERP-CORRECT))
     (448 28 (:REWRITE |(+ y (+ x z))|))
     (439 439
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (353 57 (:REWRITE ACL2-NUMBERP-X))
     (344 344
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (344 344
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (344 344 (:REWRITE |(< (/ x) 0)|))
     (344 344 (:REWRITE |(< (* x y) 0)|))
     (335 335
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (322 322 (:TYPE-PRESCRIPTION NATP))
     (282 35 (:REWRITE MOD-ZERO . 4))
     (280 252 (:REWRITE DEFAULT-PLUS-1))
     (274 274
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (274 274
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (274 274
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (274 274 (:REWRITE |(equal c (/ x))|))
     (274 274 (:REWRITE |(equal c (- x))|))
     (274 274 (:REWRITE |(equal (/ x) c)|))
     (274 274 (:REWRITE |(equal (/ x) (/ y))|))
     (274 274 (:REWRITE |(equal (- x) c)|))
     (274 274 (:REWRITE |(equal (- x) (- y))|))
     (252 252 (:REWRITE DEFAULT-PLUS-2))
     (252 84 (:REWRITE NORMALIZE-ADDENDS))
     (245 245
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (245 245
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (245 245 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (245 245 (:REWRITE |(< 0 (/ x))|))
     (245 245 (:REWRITE |(< 0 (* x y))|))
     (224 56 (:REWRITE |(+ y x)|))
     (192 192
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (189 21 (:REWRITE RATIONALP-/))
     (178 178 (:REWRITE REDUCE-RATIONALP-+))
     (178 178 (:REWRITE RATIONALP-MINUS-X))
     (178 178 (:META META-RATIONALP-CORRECT))
     (178 35 (:REWRITE MOD-X-Y-=-X . 2))
     (178 35 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (178 35
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (156 28
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (148 13 (:REWRITE |(floor x 1)|))
     (132 28 (:REWRITE MOD-ZERO . 2))
     (88 88 (:REWRITE DEFAULT-MINUS))
     (69 53 (:REWRITE DEFAULT-FLOOR-1))
     (66 66
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (66 66
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (60 60 (:REWRITE |(- (* c x))|))
     (56 56
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (56 56 (:REWRITE |(equal (+ (- c) x) y)|))
     (56 56 (:REWRITE |(+ 0 x)|))
     (56 28 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (53 53 (:REWRITE DEFAULT-FLOOR-2))
     (40 40 (:REWRITE FLOOR-ZERO . 2))
     (40 40
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (40 40
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (40 40 (:REWRITE FLOOR-CANCEL-*-CONST))
     (40 40 (:REWRITE |(floor x (- y))| . 2))
     (40 40 (:REWRITE |(floor x (- y))| . 1))
     (40 40
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (40 40
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (40 40 (:REWRITE |(floor (- x) y)| . 2))
     (40 40 (:REWRITE |(floor (- x) y)| . 1))
     (36 36 (:REWRITE DEFAULT-MOD-1))
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
     (29 29
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (28 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (28 28 (:REWRITE |(+ x (- x))|))
     (21 21 (:REWRITE INTEGERP-/))
     (13 13 (:REWRITE |(not (equal x (/ y)))|))
     (13 13 (:REWRITE |(equal x (/ y))|))
     (13 13
         (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (13 13
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (13 13
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (13 13
         (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (13 13
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (13 13
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(RTL::MOD-0-INT
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (115 13
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (114 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (99 5 (:REWRITE MOD-X-Y-=-X . 4))
     (99 5 (:REWRITE MOD-X-Y-=-X . 3))
     (96 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (96 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (96 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (96 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (94 26 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (83 5 (:REWRITE CANCEL-MOD-+))
     (80 5 (:REWRITE RTL::MOD-DOES-NOTHING))
     (78 26
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (78 26
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (60 2 (:LINEAR MOD-BOUNDS-2))
     (52 26 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (48 5 (:REWRITE MOD-ZERO . 4))
     (42 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (34 5 (:REWRITE DEFAULT-MOD-RATIO))
     (34 5 (:REWRITE |(* (- x) y)|))
     (32 2 (:REWRITE |(+ y (+ x z))|))
     (31 1 (:LINEAR RTL::MOD-BND-2))
     (26 26 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (26 26 (:TYPE-PRESCRIPTION NATP))
     (26 26 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (26 26 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (26 26
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (26 26
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (25 25 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (25 25 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (25 25 (:REWRITE THE-FLOOR-BELOW))
     (25 25 (:REWRITE THE-FLOOR-ABOVE))
     (25 25 (:REWRITE SIMPLIFY-SUMS-<))
     (25 25
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (25 25
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (25 25
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (25 25
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (25 25
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (25 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 25 (:REWRITE INTEGERP-<-CONSTANT))
     (25 25 (:REWRITE DEFAULT-LESS-THAN-2))
     (25 25 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (25 5 (:REWRITE MOD-ZERO . 3))
     (20 18 (:REWRITE DEFAULT-PLUS-1))
     (19 19 (:REWRITE DEFAULT-TIMES-2))
     (19 19 (:REWRITE DEFAULT-TIMES-1))
     (18 18 (:REWRITE DEFAULT-PLUS-2))
     (18 6 (:REWRITE NORMALIZE-ADDENDS))
     (16 4 (:REWRITE |(+ y x)|))
     (16 1 (:REWRITE |(integerp (- x))|))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (14 14
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (14 14 (:REWRITE DEFAULT-DIVIDE))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
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
     (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (11 7 (:REWRITE DEFAULT-MINUS))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< 0 (/ x))|))
     (10 10 (:REWRITE |(< 0 (* x y))|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (9 5 (:REWRITE MOD-X-Y-=-X . 2))
     (9 5
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (9 5 (:REWRITE MOD-CANCEL-*-CONST))
     (9 5
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (9 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (9 5
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (9 5
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (6 2 (:REWRITE MOD-ZERO . 2))
     (5 5
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (5 5 (:REWRITE DEFAULT-MOD-2))
     (5 5 (:REWRITE DEFAULT-MOD-1))
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
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(+ 0 x)|))
     (4 4 (:DEFINITION FIX))
     (4 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (3 3 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(+ x (- x))|))
     (1 1
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1 (:LINEAR MOD-BOUNDS-3)))
(RTL::MOD-MULT-N
     (3306 89 (:REWRITE DEFAULT-PLUS-2))
     (2747 4 (:REWRITE FLOOR-=-X/Y . 4))
     (2607 2607
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2607 2607
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2607 2607
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1556 220 (:REWRITE ACL2-NUMBERP-X))
     (1007 14 (:REWRITE FLOOR-ZERO . 3))
     (981 89 (:REWRITE DEFAULT-PLUS-1))
     (881 293 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (881 293 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (881 293 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (881 293
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (852 213 (:REWRITE RATIONALP-X))
     (785 16 (:REWRITE RTL::MOD-DOES-NOTHING))
     (738 35 (:REWRITE DEFAULT-MINUS))
     (714 14 (:REWRITE FLOOR-ZERO . 5))
     (714 14 (:REWRITE FLOOR-ZERO . 4))
     (690 14 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (678 14 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (673 14 (:REWRITE CANCEL-FLOOR-+))
     (574 14 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (574 14 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (488 4 (:LINEAR MOD-BOUNDS-2))
     (488 4 (:LINEAR MOD-BOUNDS-1))
     (439 287 (:REWRITE DEFAULT-DIVIDE))
     (387 174 (:REWRITE |(equal (- x) (- y))|))
     (371 13 (:REWRITE |(< (if a b c) x)|))
     (350 14 (:REWRITE FLOOR-=-X/Y . 3))
     (323 14 (:REWRITE FLOOR-ZERO . 2))
     (310 14 (:REWRITE FLOOR-=-X/Y . 2))
     (296 15 (:REWRITE |(* (- x) y)|))
     (289 289 (:REWRITE REDUCE-INTEGERP-+))
     (289 289 (:REWRITE INTEGERP-MINUS-X))
     (289 289 (:META META-INTEGERP-CORRECT))
     (287 4 (:REWRITE MOD-X-Y-=-X . 4))
     (287 4 (:REWRITE MOD-X-Y-=-X . 3))
     (286 14
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (284 14 (:REWRITE FLOOR-CANCEL-*-CONST))
     (284 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (280 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (277 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (275 275
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (251 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (251 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (238 142
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (230 14
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (230 14
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (219 4 (:REWRITE MOD-ZERO . 4))
     (218 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (213 213 (:REWRITE REDUCE-RATIONALP-+))
     (213 213 (:REWRITE REDUCE-RATIONALP-*))
     (213 213 (:REWRITE RATIONALP-MINUS-X))
     (213 213 (:META META-RATIONALP-CORRECT))
     (206 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (203 4 (:REWRITE MOD-X-Y-=-X . 2))
     (203 4
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (190 156 (:REWRITE DEFAULT-LESS-THAN-1))
     (187 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (182 4 (:REWRITE MOD-ZERO . 3))
     (180 6 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (174 174
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (174 174
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (174 174 (:REWRITE |(equal c (/ x))|))
     (174 174 (:REWRITE |(equal (/ x) (/ y))|))
     (172 4
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (170 170
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (170 170 (:REWRITE |(equal c (- x))|))
     (170 170 (:REWRITE |(equal (- x) c)|))
     (161 161 (:REWRITE THE-FLOOR-BELOW))
     (161 161 (:REWRITE THE-FLOOR-ABOVE))
     (158 158
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (148 4 (:REWRITE MOD-CANCEL-*-CONST))
     (148 4
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (148 4
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (142 142 (:REWRITE SIMPLIFY-SUMS-<))
     (142 142
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (142 142
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (142 142
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (142 142
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (142 142
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (142 142 (:REWRITE INTEGERP-<-CONSTANT))
     (142 142 (:REWRITE CONSTANT-<-INTEGERP))
     (142 142
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (142 142
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (142 142
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (142 142
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (142 142 (:REWRITE |(< c (- x))|))
     (142 142
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (142 142
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (142 142
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (142 142
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (142 142 (:REWRITE |(< (/ x) (/ y))|))
     (142 142 (:REWRITE |(< (- x) c)|))
     (142 142 (:REWRITE |(< (- x) (- y))|))
     (125 14
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (108 6 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (68 68 (:REWRITE |(< (/ x) 0)|))
     (68 68 (:REWRITE |(< (* x y) 0)|))
     (68 14
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (68 14
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (64 2 (:LINEAR RTL::MOD-BND-2))
     (61 61 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (57 4 (:REWRITE CANCEL-MOD-+))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (52 52 (:REWRITE |(< 0 (/ x))|))
     (52 52 (:REWRITE |(< 0 (* x y))|))
     (48 12 (:REWRITE |(integerp (- x))|))
     (32 28
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (32 28
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (32 8 (:REWRITE MOD-MULT-2))
     (28 28 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (28 28 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (28 28
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (28 28
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (27 27
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (27 27 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (27 27 (:TYPE-PRESCRIPTION NATP))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (27 27
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (27 3 (:DEFINITION RFIX))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 2
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (20 2 (:LINEAR MOD-BOUNDS-3))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (17 17
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (16 4 (:REWRITE |(floor x 1)|))
     (14 14 (:REWRITE DEFAULT-FLOOR-2))
     (14 14 (:REWRITE DEFAULT-FLOOR-1))
     (14 14 (:REWRITE |(floor x (- y))| . 2))
     (14 14 (:REWRITE |(floor x (- y))| . 1))
     (14 14 (:REWRITE |(floor (- x) y)| . 2))
     (14 14 (:REWRITE |(floor (- x) y)| . 1))
     (13 13
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (12 3 (:REWRITE RTL::MOD-BY-1))
     (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
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
     (4 4 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(- (* c x))|))
     (4 1 (:REWRITE |(mod x 1)|))
     (3 3 (:REWRITE |(equal (* x y) 0)|))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::MOD-MULT-N-ALT
     (1130 138 (:REWRITE ACL2-NUMBERP-X))
     (697 17 (:REWRITE RTL::MOD-DOES-NOTHING))
     (596 149 (:REWRITE RATIONALP-X))
     (580 4 (:LINEAR MOD-BOUNDS-2))
     (580 4 (:LINEAR MOD-BOUNDS-1))
     (292 4 (:REWRITE MOD-X-Y-=-X . 4))
     (292 4 (:REWRITE MOD-X-Y-=-X . 3))
     (286 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (280 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (278 10 (:REWRITE |(< (if a b c) x)|))
     (228 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (228 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (224 4 (:REWRITE MOD-ZERO . 4))
     (208 56 (:REWRITE DEFAULT-DIVIDE))
     (196 4 (:REWRITE MOD-X-Y-=-X . 2))
     (196 4
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (194 4 (:REWRITE MOD-ZERO . 3))
     (180 68 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (180 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (161 161 (:REWRITE REDUCE-INTEGERP-+))
     (161 161 (:REWRITE INTEGERP-MINUS-X))
     (161 161 (:META META-INTEGERP-CORRECT))
     (154 4
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (154 4 (:REWRITE MOD-CANCEL-*-CONST))
     (149 149 (:REWRITE REDUCE-RATIONALP-+))
     (149 149 (:REWRITE REDUCE-RATIONALP-*))
     (149 149 (:REWRITE RATIONALP-MINUS-X))
     (149 149 (:META META-RATIONALP-CORRECT))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (113 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (100 12 (:REWRITE |(+ y x)|))
     (99 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (94 78 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (94 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (89 49
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (83 79
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (83 79
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (79 79 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (79 79 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (79 79
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (79 79
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (78 78 (:TYPE-PRESCRIPTION NATP))
     (78 78 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (78 78 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (78 78 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (78 78
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (74 74
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (74 74
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (72 72 (:REWRITE |(equal c (/ x))|))
     (72 72 (:REWRITE |(equal (/ x) (/ y))|))
     (72 72 (:REWRITE |(equal (- x) (- y))|))
     (70 70
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (70 70 (:REWRITE |(equal c (- x))|))
     (70 70 (:REWRITE |(equal (- x) c)|))
     (68 68
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (64 64 (:REWRITE THE-FLOOR-BELOW))
     (64 64 (:REWRITE THE-FLOOR-ABOVE))
     (64 64
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (64 2 (:LINEAR RTL::MOD-BND-2))
     (62 14 (:REWRITE NORMALIZE-ADDENDS))
     (59 59 (:REWRITE DEFAULT-LESS-THAN-1))
     (58 4 (:REWRITE CANCEL-MOD-+))
     (52 4 (:REWRITE |(+ y (+ x z))|))
     (49 49 (:REWRITE SIMPLIFY-SUMS-<))
     (49 49
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (49 49
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (49 49
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (49 49
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (49 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (49 49 (:REWRITE INTEGERP-<-CONSTANT))
     (49 49 (:REWRITE CONSTANT-<-INTEGERP))
     (49 49
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (49 49
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (49 49
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (49 49
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (49 49 (:REWRITE |(< c (- x))|))
     (49 49
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (49 49
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (49 49
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (49 49
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (49 49 (:REWRITE |(< (/ x) (/ y))|))
     (49 49 (:REWRITE |(< (- x) c)|))
     (49 49 (:REWRITE |(< (- x) (- y))|))
     (47 47
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (46 46
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (46 38 (:REWRITE DEFAULT-PLUS-1))
     (38 38 (:REWRITE DEFAULT-PLUS-2))
     (36 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (31 31 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (20 2 (:LINEAR MOD-BOUNDS-3))
     (17 5 (:REWRITE RTL::MOD-BY-1))
     (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (16 2 (:REWRITE |(* (- x) y)|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE |(+ x (- x))|))
     (8 2 (:REWRITE |(mod x 1)|))
     (8 2 (:REWRITE |(integerp (- x))|))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE |(mod x (- y))| . 3))
     (4 4 (:REWRITE |(mod x (- y))| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 1))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(mod (- x) y)| . 3))
     (4 4 (:REWRITE |(mod (- x) y)| . 2))
     (4 4 (:REWRITE |(mod (- x) y)| . 1))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2 (:REWRITE |(equal (* x y) 0)|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(equal (mod (+ x y) z) x)|)))
(RTL::MOD-SQUEEZE
     (668 668
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (668 668
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (668 668
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (360 72 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (352 12 (:REWRITE MOD-X-Y-=-X . 4))
     (352 12 (:REWRITE MOD-X-Y-=-X . 3))
     (342 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (342 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (342 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (342 12 (:REWRITE CANCEL-MOD-+))
     (318 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (299 299 (:REWRITE DEFAULT-TIMES-2))
     (299 299 (:REWRITE DEFAULT-TIMES-1))
     (262 12 (:REWRITE RTL::MOD-DOES-NOTHING))
     (253 55
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (232 72 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (220 72
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (220 72
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (212 12 (:REWRITE MOD-ZERO . 3))
     (204 6 (:LINEAR MOD-BOUNDS-2))
     (182 12 (:REWRITE MOD-ZERO . 4))
     (182 12 (:REWRITE MOD-X-Y-=-X . 2))
     (177 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (128 8 (:REWRITE |(integerp (- x))|))
     (127 64 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (126 126 (:REWRITE THE-FLOOR-BELOW))
     (126 126 (:REWRITE THE-FLOOR-ABOVE))
     (126 126
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (126 126
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (126 126
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (126 126 (:REWRITE DEFAULT-LESS-THAN-2))
     (126 126 (:REWRITE DEFAULT-LESS-THAN-1))
     (124 124
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (124 124 (:REWRITE INTEGERP-<-CONSTANT))
     (124 124 (:REWRITE CONSTANT-<-INTEGERP))
     (124 124
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (124 124
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (124 124
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (124 124
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (124 124 (:REWRITE |(< c (- x))|))
     (124 124
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (124 124
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (124 124
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (124 124
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (124 124 (:REWRITE |(< (/ x) (/ y))|))
     (124 124 (:REWRITE |(< (- x) c)|))
     (124 124 (:REWRITE |(< (- x) (- y))|))
     (120 12 (:REWRITE DEFAULT-MOD-RATIO))
     (98 90 (:REWRITE DEFAULT-PLUS-1))
     (93 3 (:LINEAR RTL::MOD-BND-2))
     (91 4
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (91 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (90 90 (:REWRITE DEFAULT-PLUS-2))
     (82 82
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (81 9 (:REWRITE |(* (- x) y)|))
     (78 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (78 12
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (75 3 (:REWRITE MOD-ZERO . 1))
     (72 72 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (72 72 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (72 72
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (72 72 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (72 72
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (72 58 (:REWRITE |(equal (/ x) c)|))
     (69 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (64 64 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (63 63 (:TYPE-PRESCRIPTION NATP))
     (63 63 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (63 3 (:LINEAR MOD-BOUNDS-3))
     (60 12
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (60 12
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (60 12
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (58 58
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (58 58
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (58 58 (:REWRITE |(equal c (/ x))|))
     (58 58 (:REWRITE |(equal (/ x) (/ y))|))
     (58 58 (:REWRITE |(equal (- x) (- y))|))
     (57 57
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (57 57
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (57 57
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (57 57 (:REWRITE |(equal c (- x))|))
     (57 57 (:REWRITE |(equal (- x) c)|))
     (57 57 (:REWRITE |(< (/ x) 0)|))
     (57 57 (:REWRITE |(< (* x y) 0)|))
     (56 56 (:REWRITE DEFAULT-DIVIDE))
     (55 55
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (54 3 (:REWRITE MOD-ZERO . 2))
     (52 52 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (52 12 (:REWRITE MOD-CANCEL-*-CONST))
     (44 44
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (44 12 (:REWRITE DEFAULT-MINUS))
     (41 41 (:REWRITE REDUCE-INTEGERP-+))
     (41 41 (:REWRITE INTEGERP-MINUS-X))
     (41 41 (:META META-INTEGERP-CORRECT))
     (35 35 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (35 35 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (32 32 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (31 31 (:REWRITE |(< 0 (* x y))|))
     (29 29 (:REWRITE |(< 0 (/ x))|))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (27 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (25 25
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (13 13 (:REWRITE |(< y (+ (- c) x))|))
     (13 13 (:REWRITE |(< x (+ c/d y))|))
     (12 12
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (12 12 (:REWRITE DEFAULT-MOD-2))
     (12 12 (:REWRITE DEFAULT-MOD-1))
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
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE |(- (* c x))|))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(equal (* x y) 0)|))
     (1 1 (:REWRITE |(/ (/ x))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(* x (- y))|)))
(RTL::MOD-MUST-BE-N
     (572 572
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (572 572
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (572 572
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (390 10 (:REWRITE CANCEL-MOD-+))
     (240 48 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (208 10 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (208 10 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (190 10 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (184 10 (:REWRITE MOD-X-Y-=-X . 3))
     (176 176 (:REWRITE DEFAULT-TIMES-2))
     (176 176 (:REWRITE DEFAULT-TIMES-1))
     (160 10 (:REWRITE RTL::MOD-DOES-NOTHING))
     (160 10 (:REWRITE |(integerp (- x))|))
     (156 48 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (152 28
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (148 48
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (148 48
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (140 48 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (136 4 (:LINEAR MOD-BOUNDS-2))
     (130 10 (:REWRITE MOD-ZERO . 3))
     (112 10 (:REWRITE MOD-X-Y-=-X . 2))
     (100 10 (:REWRITE DEFAULT-MOD-RATIO))
     (100 10 (:REWRITE |(* (- x) y)|))
     (95 48 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (94 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (90 3
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (90 3
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (68 68 (:REWRITE THE-FLOOR-BELOW))
     (68 68 (:REWRITE THE-FLOOR-ABOVE))
     (68 68
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (68 68
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (68 68
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (68 68 (:REWRITE DEFAULT-LESS-THAN-2))
     (68 68 (:REWRITE DEFAULT-LESS-THAN-1))
     (68 68
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (68 68
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (68 68
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (68 68
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (68 68
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (68 68
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (68 68
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (68 68
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (68 68 (:REWRITE |(< (/ x) (/ y))|))
     (68 68 (:REWRITE |(< (- x) (- y))|))
     (66 66
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (66 66 (:REWRITE INTEGERP-<-CONSTANT))
     (66 66 (:REWRITE CONSTANT-<-INTEGERP))
     (66 66 (:REWRITE |(< c (- x))|))
     (66 66 (:REWRITE |(< (- x) c)|))
     (65 65 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (59 53 (:REWRITE DEFAULT-PLUS-1))
     (53 53
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (53 53 (:REWRITE DEFAULT-PLUS-2))
     (52 12 (:REWRITE DEFAULT-MINUS))
     (50 10 (:REWRITE MOD-ZERO . 4))
     (50 10 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (50 10 (:REWRITE MOD-X-Y-=-X . 4))
     (50 10
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (50 10
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (50 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (50 10
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (50 10
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (50 2 (:REWRITE MOD-ZERO . 1))
     (48 48 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (48 48 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (48 48
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (48 48 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (48 48
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (48 48
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (47 47 (:TYPE-PRESCRIPTION NATP))
     (47 47 (:REWRITE DEFAULT-DIVIDE))
     (46 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (45 31 (:REWRITE |(equal (/ x) c)|))
     (44 44
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (42 2 (:LINEAR MOD-BOUNDS-3))
     (36 2 (:REWRITE MOD-ZERO . 2))
     (34 10 (:REWRITE MOD-CANCEL-*-CONST))
     (31 31
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (31 31
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (31 31 (:REWRITE |(equal c (/ x))|))
     (31 31 (:REWRITE |(equal (/ x) (/ y))|))
     (31 31 (:REWRITE |(equal (- x) (- y))|))
     (30 30
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (30 30 (:REWRITE |(equal c (- x))|))
     (30 30 (:REWRITE |(equal (- x) c)|))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:META META-INTEGERP-CORRECT))
     (27 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (26 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (24 6 (:REWRITE RATIONALP-X))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (21 21 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (17 17 (:REWRITE |(< 0 (* x y))|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (10 10
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (10 10 (:REWRITE DEFAULT-MOD-2))
     (10 10 (:REWRITE DEFAULT-MOD-1))
     (10 10 (:REWRITE |(mod x (- y))| . 3))
     (10 10 (:REWRITE |(mod x (- y))| . 2))
     (10 10 (:REWRITE |(mod x (- y))| . 1))
     (10 10
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (10 10 (:REWRITE |(mod (- x) y)| . 3))
     (10 10 (:REWRITE |(mod (- x) y)| . 2))
     (10 10 (:REWRITE |(mod (- x) y)| . 1))
     (10 10
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (10 10 (:REWRITE |(- (* c x))|))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::MOD-0-0
     (15080 15080
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (15080 15080
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (15080 15080
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7344 2441 (:REWRITE DEFAULT-TIMES-2))
     (4812 597 (:REWRITE DEFAULT-PLUS-2))
     (4418 18 (:REWRITE FLOOR-ZERO . 3))
     (4340 520
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (4340 520
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (4182 490
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (4182 490
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3756 1092
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (3756 1092
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (3756 1092
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (3735 18 (:REWRITE CANCEL-FLOOR-+))
     (3152 3152
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3152 3152
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3152 3152
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (3072 2441 (:REWRITE DEFAULT-TIMES-1))
     (2866 597 (:REWRITE DEFAULT-PLUS-1))
     (2544 520 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (2544 520
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (2544 520
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (2544 520
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (2544 520
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (2450 490 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (2450 490
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (2450 490
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (2450 490
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (2450 490
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (2143 18 (:REWRITE |(integerp (- x))|))
     (2042 18 (:REWRITE FLOOR-=-X/Y . 2))
     (1973 120 (:REWRITE |(< (/ x) 0)|))
     (1634 686
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (1634 686
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (1634 686
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (1594 18 (:REWRITE FLOOR-=-X/Y . 3))
     (1540 158
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1082 502 (:REWRITE DEFAULT-DIVIDE))
     (1053 23 (:REWRITE DEFAULT-MINUS))
     (1021 1021
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (967 237 (:META META-INTEGERP-CORRECT))
     (916 21 (:REWRITE DEFAULT-FLOOR-RATIO))
     (815 241 (:REWRITE DEFAULT-LESS-THAN-1))
     (792 18 (:REWRITE FLOOR-ZERO . 4))
     (790 18 (:REWRITE FLOOR-ZERO . 5))
     (788 36 (:LINEAR RTL::FL-DEF))
     (751 18 (:REWRITE |(* (- x) y)|))
     (686 686
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
     (686 686
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
     (686 686
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
     (669 162 (:REWRITE |(equal (- x) (- y))|))
     (665 158 (:REWRITE |(equal (- x) c)|))
     (625 18 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (625 18 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (625 18 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (625 18 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (560 53 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (553 72 (:REWRITE INTEGERP-/))
     (537 230
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (445 230
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (405 405
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4F))
     (405 405
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3F))
     (405 405
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2F))
     (405 405
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1F))
     (400 400
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (374 241 (:REWRITE DEFAULT-LESS-THAN-2))
     (337 18 (:REWRITE FLOOR-ZERO . 2))
     (282 5 (:REWRITE MOD-ZERO . 4))
     (281 5 (:REWRITE MOD-X-Y-=-X . 3))
     (279 5 (:REWRITE MOD-X-Y-=-X . 4))
     (278 5 (:REWRITE RTL::MOD-DOES-NOTHING))
     (246 246 (:REWRITE |(* c (* d x))|))
     (244 5 (:REWRITE MOD-ZERO . 3))
     (241 241 (:REWRITE THE-FLOOR-BELOW))
     (241 241 (:REWRITE THE-FLOOR-ABOVE))
     (241 241
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (241 241
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (241 241
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (241 241
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (241 241
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (241 241
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (241 241
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (241 241
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (241 241
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (241 241
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (241 241
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (241 241 (:REWRITE |(< (/ x) (/ y))|))
     (241 241 (:REWRITE |(< (- x) (- y))|))
     (237 237 (:REWRITE REDUCE-INTEGERP-+))
     (237 237 (:REWRITE INTEGERP-MINUS-X))
     (230 230
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (230 230 (:REWRITE INTEGERP-<-CONSTANT))
     (230 230 (:REWRITE CONSTANT-<-INTEGERP))
     (230 230 (:REWRITE |(< c (- x))|))
     (230 230 (:REWRITE |(< (- x) c)|))
     (230 46 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (218 162 (:REWRITE |(equal (/ x) c)|))
     (214 46 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (201 201
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (194 46
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (194 46
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (173 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (173 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (173 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (173 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (162 162
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (162 162
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (162 162 (:REWRITE |(equal c (/ x))|))
     (162 162 (:REWRITE |(equal (/ x) (/ y))|))
     (158 158
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (158 158 (:REWRITE |(equal c (- x))|))
     (132 132 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (126 5 (:REWRITE DEFAULT-MOD-RATIO))
     (120 120 (:REWRITE |(< (* x y) 0)|))
     (109 109
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (109 109
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (108 108
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (108 27 (:REWRITE RATIONALP-X))
     (95 5 (:REWRITE MOD-X-Y-=-X . 2))
     (95 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (95 5
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (93 18
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (93 18 (:REWRITE FLOOR-CANCEL-*-CONST))
     (93 18
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (92 46 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (86 86
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (86 86
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (86 86 (:REWRITE |(< 0 (/ x))|))
     (86 86 (:REWRITE |(< 0 (* x y))|))
     (73 5 (:REWRITE CANCEL-MOD-+))
     (62 62
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (46 46 (:TYPE-PRESCRIPTION NATP))
     (46 46 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (46 46 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (46 46
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (46 46 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (46 46 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (46 46
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (37 37
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (36 36 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (32 32 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (32 32 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (30 1 (:REWRITE MOD-X-I*J))
     (27 27 (:REWRITE REDUCE-RATIONALP-+))
     (27 27 (:REWRITE REDUCE-RATIONALP-*))
     (27 27 (:REWRITE RATIONALP-MINUS-X))
     (27 27 (:META META-RATIONALP-CORRECT))
     (27 5
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (27 5 (:REWRITE MOD-CANCEL-*-CONST))
     (27 5
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (27 5
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (26 26 (:REWRITE |(/ (/ x))|))
     (24 1 (:REWRITE |(* (if a b c) x)|))
     (23 23 (:REWRITE |(- (* c x))|))
     (22 22 (:REWRITE DEFAULT-FLOOR-2))
     (22 22 (:REWRITE |(< (+ c/d x) y)|))
     (22 22 (:REWRITE |(< (+ (- c) x) y)|))
     (20 4 (:REWRITE ACL2-NUMBERP-X))
     (18 18
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (18 18 (:REWRITE |(floor x (- y))| . 2))
     (18 18 (:REWRITE |(floor x (- y))| . 1))
     (18 18
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (18 18 (:REWRITE |(floor (- x) y)| . 2))
     (18 18 (:REWRITE |(floor (- x) y)| . 1))
     (18 18 (:LINEAR RTL::N<=FL-LINEAR))
     (17 17
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (17 17 (:REWRITE |(equal (* x y) 0)|))
     (16 16 (:REWRITE |(+ c (+ d x))|))
     (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
     (7 5 (:REWRITE DEFAULT-MOD-1))
     (5 5
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (5 5 (:REWRITE DEFAULT-MOD-2))
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
     (5 5
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 1 (:REWRITE MOD-X-I*J-V2))
     (3 3 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1 1
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|)))
(RTL::MOD-EQUAL-INT
     (9173 348 (:REWRITE MOD-X-Y-=-X . 4))
     (8488 348 (:REWRITE MOD-X-Y-=-X . 3))
     (8338 354 (:REWRITE RTL::MOD-DOES-NOTHING))
     (6756 80 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (6041 6041
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (6041 6041
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (6041 6041
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5558 348 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (5048 348 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (4992 2501 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (4982 879
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4967 348 (:REWRITE CANCEL-MOD-+))
     (4352 348 (:REWRITE MOD-ZERO . 4))
     (4205 348 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (4002 3939 (:REWRITE DEFAULT-TIMES-2))
     (3960 3939 (:REWRITE DEFAULT-TIMES-1))
     (3915 348 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (3276 3276
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3151 476 (:REWRITE RATIONALP-X))
     (2967 80 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (2953 348 (:REWRITE MOD-ZERO . 3))
     (2501 2501
           (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (2501 2501 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (2501 2501 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2501 2501
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (2493 2493
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2493 2493
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2491 2491 (:TYPE-PRESCRIPTION NATP))
     (2450 1933 (:REWRITE DEFAULT-PLUS-2))
     (2234 2234
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2233 2233
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2102 1933 (:REWRITE DEFAULT-PLUS-1))
     (1987 1987 (:REWRITE THE-FLOOR-BELOW))
     (1987 1987 (:REWRITE THE-FLOOR-ABOVE))
     (1972 1968 (:REWRITE DEFAULT-LESS-THAN-1))
     (1968 1928
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1959 1959
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1959 1959
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1947 1947 (:REWRITE INTEGERP-<-CONSTANT))
     (1947 1947 (:REWRITE CONSTANT-<-INTEGERP))
     (1947 1947
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1947 1947
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1947 1947
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1947 1947
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1947 1947 (:REWRITE |(< c (- x))|))
     (1947 1947
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1947 1947
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1947 1947
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1947 1947
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1947 1947 (:REWRITE |(< (/ x) (/ y))|))
     (1947 1947 (:REWRITE |(< (- x) c)|))
     (1947 1947 (:REWRITE |(< (- x) (- y))|))
     (1944 1928
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1818 1818
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1614 269 (:REWRITE |(* (- x) y)|))
     (1374 879
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1316 1316
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1224 834 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1037 348 (:REWRITE MOD-X-Y-=-X . 2))
     (1037 348
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (1037 348
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (986 986 (:REWRITE INTEGERP-MINUS-X))
     (974 974 (:META META-INTEGERP-CORRECT))
     (894 880 (:REWRITE |(equal (/ x) c)|))
     (880 880
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (880 880
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (880 880 (:REWRITE |(equal c (/ x))|))
     (880 880 (:REWRITE |(equal (/ x) (/ y))|))
     (880 880 (:REWRITE |(equal (- x) (- y))|))
     (879 879
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (879 879 (:REWRITE |(equal c (- x))|))
     (879 879 (:REWRITE |(equal (- x) c)|))
     (813 813 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (770 770
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (740 740
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (670 57 (:LINEAR MOD-BOUNDS-3))
     (646 646 (:REWRITE |(< (* x y) 0)|))
     (640 640 (:REWRITE |(< (/ x) 0)|))
     (634 634
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (634 634
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (624 624 (:REWRITE |(< 0 (/ x))|))
     (624 624 (:REWRITE |(< 0 (* x y))|))
     (617 617
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (617 617
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (473 57 (:REWRITE ACL2-NUMBERP-X))
     (422 78
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (412 412 (:REWRITE RATIONALP-MINUS-X))
     (383 383 (:META META-RATIONALP-CORRECT))
     (368 368 (:REWRITE DEFAULT-MINUS))
     (351 351 (:REWRITE DEFAULT-MOD-1))
     (348 348
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (348 348
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (348 348 (:REWRITE MOD-CANCEL-*-CONST))
     (348 348 (:REWRITE |(mod x (- y))| . 3))
     (348 348 (:REWRITE |(mod x (- y))| . 2))
     (348 348 (:REWRITE |(mod x (- y))| . 1))
     (348 348
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (348 348
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (348 348 (:REWRITE |(mod (- x) y)| . 3))
     (348 348 (:REWRITE |(mod (- x) y)| . 2))
     (348 348 (:REWRITE |(mod (- x) y)| . 1))
     (348 348
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (348 348
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (309 309 (:REWRITE |(- (* c x))|))
     (167 63 (:REWRITE MOD-ZERO . 2))
     (165 165 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (120 3
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (83 83 (:REWRITE |(equal (+ (- c) x) y)|))
     (64 64 (:REWRITE INTEGERP-/))
     (57 57 (:REWRITE |(< (+ c/d x) y)|))
     (54 6
         (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (54 6
         (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (51 51 (:REWRITE |(< (+ (- c) x) y)|))
     (48 48
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (25 25 (:REWRITE |(not (equal x (/ y)))|))
     (25 25 (:REWRITE |(equal x (/ y))|))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (15 15 (:REWRITE |(< y (+ (- c) x))|))
     (15 15 (:REWRITE |(< x (+ c/d y))|))
     (12 12
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (8 8 (:REWRITE MOD-NEGATIVE . 3))
     (8 8 (:REWRITE MOD-NEGATIVE . 2))
     (7 7 (:REWRITE MOD-POSITIVE . 3))
     (7 7 (:REWRITE MOD-POSITIVE . 2)))
(RTL::MOD-EQUAL-INT-REVERSE
     (746 746
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (746 746
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (746 746
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (546 14 (:REWRITE CANCEL-MOD-+))
     (490 14 (:REWRITE MOD-X-Y-=-X . 4))
     (490 14 (:REWRITE MOD-X-Y-=-X . 3))
     (476 14 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (434 14 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (378 82
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (378 82
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (364 14 (:REWRITE RTL::MOD-DOES-NOTHING))
     (294 14 (:REWRITE MOD-ZERO . 3))
     (252 14 (:REWRITE MOD-ZERO . 4))
     (240 15 (:REWRITE |(integerp (- x))|))
     (164 82 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (140 14 (:REWRITE DEFAULT-MOD-RATIO))
     (140 14 (:REWRITE |(* (- x) y)|))
     (124 4 (:LINEAR RTL::MOD-BND-2))
     (84 4 (:LINEAR MOD-BOUNDS-3))
     (82 82 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (82 82 (:TYPE-PRESCRIPTION NATP))
     (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (82 82
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (82 82
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (82 82
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (76 16 (:REWRITE DEFAULT-MINUS))
     (75 75 (:REWRITE THE-FLOOR-BELOW))
     (75 75 (:REWRITE THE-FLOOR-ABOVE))
     (75 75 (:REWRITE SIMPLIFY-SUMS-<))
     (75 75
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (75 75
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (75 75
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (75 75
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (75 75
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (75 75 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (75 75 (:REWRITE INTEGERP-<-CONSTANT))
     (75 75 (:REWRITE DEFAULT-LESS-THAN-2))
     (75 75 (:REWRITE DEFAULT-LESS-THAN-1))
     (75 75 (:REWRITE CONSTANT-<-INTEGERP))
     (75 75
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (75 75
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (75 75
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (75 75
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (75 75 (:REWRITE |(< c (- x))|))
     (75 75
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (75 75
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (75 75
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (75 75
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (75 75 (:REWRITE |(< (/ x) (/ y))|))
     (75 75 (:REWRITE |(< (- x) c)|))
     (75 75 (:REWRITE |(< (- x) (- y))|))
     (70 14 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (70 14 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (70 14 (:REWRITE MOD-X-Y-=-X . 2))
     (70 14
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (70 14 (:REWRITE MOD-CANCEL-*-CONST))
     (70 14
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (70 14 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (70 14
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (70 14
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (67 67 (:REWRITE DEFAULT-TIMES-2))
     (67 67 (:REWRITE DEFAULT-TIMES-1))
     (67 38 (:REWRITE REDUCE-INTEGERP-+))
     (49 49
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (47 47 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (47 47
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (47 47 (:REWRITE DEFAULT-DIVIDE))
     (42 38 (:REWRITE INTEGERP-MINUS-X))
     (40 8 (:LINEAR MOD-BOUNDS-2))
     (38 38 (:META META-INTEGERP-CORRECT))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (32 32 (:REWRITE |(< (/ x) 0)|))
     (32 32 (:REWRITE |(< (* x y) 0)|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (15 15 (:REWRITE |(- (* c x))|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (14 14
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE DEFAULT-MOD-2))
     (14 14 (:REWRITE DEFAULT-MOD-1))
     (14 14 (:REWRITE |(mod x (- y))| . 3))
     (14 14 (:REWRITE |(mod x (- y))| . 2))
     (14 14 (:REWRITE |(mod x (- y))| . 1))
     (14 14
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(mod (- x) y)| . 3))
     (14 14 (:REWRITE |(mod (- x) y)| . 2))
     (14 14 (:REWRITE |(mod (- x) y)| . 1))
     (14 14
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (12 3 (:REWRITE RATIONALP-X))
     (6 2 (:REWRITE DEFAULT-PLUS-2))
     (6 2 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (1 1
        (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RTL::MOD-FORCE-EQUAL
     (12071 12071
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (12071 12071
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (10424 348 (:REWRITE MOD-X-Y-=-X . 4))
     (9318 2506 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (9246 348 (:REWRITE CANCEL-MOD-+))
     (9238 352 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (8480 369 (:REWRITE RTL::MOD-DOES-NOTHING))
     (7934 348 (:REWRITE MOD-X-Y-=-X . 3))
     (6702 2506 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (6494 2506
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (5874 28 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (5086 348 (:REWRITE MOD-ZERO . 4))
     (4986 2506 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (4613 523
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3701 3701 (:REWRITE DEFAULT-TIMES-2))
     (3701 3701 (:REWRITE DEFAULT-TIMES-1))
     (3628 348 (:REWRITE MOD-ZERO . 3))
     (3104 194 (:REWRITE |(integerp (- x))|))
     (2968 28 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (2908 352 (:REWRITE DEFAULT-MOD-RATIO))
     (2840 344 (:REWRITE |(* (- x) y)|))
     (2506 2506
           (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (2506 2506
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (2506 2506
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2506 2506
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2506 2506
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2506 2506
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (2505 2505 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2480 2480 (:TYPE-PRESCRIPTION NATP))
     (2385 2385
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (2385 2385
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (2150 352 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (2125 1655 (:REWRITE DEFAULT-PLUS-2))
     (2084 352 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1991 1991 (:REWRITE THE-FLOOR-BELOW))
     (1991 1991 (:REWRITE THE-FLOOR-ABOVE))
     (1991 1975 (:REWRITE DEFAULT-LESS-THAN-2))
     (1975 1975 (:REWRITE DEFAULT-LESS-THAN-1))
     (1966 1966
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1966 1966
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1942 1942 (:REWRITE INTEGERP-<-CONSTANT))
     (1942 1942 (:REWRITE CONSTANT-<-INTEGERP))
     (1942 1942
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1942 1942
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1942 1942
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1942 1942
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1942 1942 (:REWRITE |(< c (- x))|))
     (1942 1942
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1942 1942
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1942 1942
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1942 1942
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1942 1942 (:REWRITE |(< (/ x) (/ y))|))
     (1942 1942 (:REWRITE |(< (- x) c)|))
     (1942 1942 (:REWRITE |(< (- x) (- y))|))
     (1864 1864
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1828 1655 (:REWRITE DEFAULT-PLUS-1))
     (1784 86 (:LINEAR MOD-BOUNDS-2))
     (1615 1615
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1506 348 (:REWRITE MOD-X-Y-=-X . 2))
     (1184 1184 (:REWRITE DEFAULT-DIVIDE))
     (1179 1179
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1174 374 (:REWRITE DEFAULT-MINUS))
     (1173 1173
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1158 348
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (1158 348
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (1140 348
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1140 348
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1140 348
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (964 348 (:REWRITE MOD-CANCEL-*-CONST))
     (768 768 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (663 663
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (653 43 (:LINEAR MOD-BOUNDS-3))
     (608 538 (:REWRITE |(equal (/ x) c)|))
     (593 569 (:REWRITE INTEGERP-MINUS-X))
     (565 565 (:META META-INTEGERP-CORRECT))
     (564 564 (:REWRITE |(< (* x y) 0)|))
     (558 558 (:REWRITE |(< (/ x) 0)|))
     (557 557
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (557 557
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (538 538
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (538 538
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (538 538 (:REWRITE |(equal c (/ x))|))
     (538 538 (:REWRITE |(equal (/ x) (/ y))|))
     (538 538 (:REWRITE |(equal (- x) (- y))|))
     (533 533
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (533 533 (:REWRITE |(equal c (- x))|))
     (533 533 (:REWRITE |(equal (- x) c)|))
     (453 453 (:REWRITE |(< 0 (* x y))|))
     (441 441
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (441 441
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (441 441 (:REWRITE |(< 0 (/ x))|))
     (425 425
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (366 6
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (352 352 (:REWRITE DEFAULT-MOD-2))
     (352 352 (:REWRITE DEFAULT-MOD-1))
     (350 350 (:REWRITE |(- (* c x))|))
     (348 348
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (348 348 (:REWRITE |(mod x (- y))| . 3))
     (348 348 (:REWRITE |(mod x (- y))| . 2))
     (348 348 (:REWRITE |(mod x (- y))| . 1))
     (348 348
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (348 348 (:REWRITE |(mod (- x) y)| . 3))
     (348 348 (:REWRITE |(mod (- x) y)| . 2))
     (348 348 (:REWRITE |(mod (- x) y)| . 1))
     (348 348
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (250 10 (:REWRITE MOD-ZERO . 1))
     (192 48 (:REWRITE RATIONALP-X))
     (192 18
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (192 18
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (192 18
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (149 149 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (126 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (126 30
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (126 30
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (126 30
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (114 18
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (101 101 (:REWRITE |(< y (+ (- c) x))|))
     (101 101 (:REWRITE |(< x (+ c/d y))|))
     (91 91 (:REWRITE |(< (+ c/d x) y)|))
     (85 85 (:REWRITE |(< (+ (- c) x) y)|))
     (78 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (78 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (78 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (78 30
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (76 10 (:REWRITE MOD-ZERO . 2))
     (64 64 (:REWRITE |(equal (+ (- c) x) y)|))
     (48 48 (:REWRITE REDUCE-RATIONALP-+))
     (48 48 (:REWRITE REDUCE-RATIONALP-*))
     (48 48 (:REWRITE RATIONALP-MINUS-X))
     (48 48 (:META META-RATIONALP-CORRECT))
     (30 30 (:REWRITE FOLD-CONSTS-IN-+))
     (28 28
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (12 12
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (10 10
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (8 8 (:REWRITE MOD-POSITIVE . 3))
     (8 8 (:REWRITE MOD-POSITIVE . 2))
     (8 8 (:REWRITE MOD-NEGATIVE . 3))
     (8 8 (:REWRITE MOD-NEGATIVE . 2))
     (6 6
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (5 5 (:REWRITE |(not (equal x (/ y)))|))
     (5 5 (:REWRITE |(equal x (/ y))|)))
(RTL::CONGRUENT (50 10 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (20 10 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
                (10 10
                    (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
                (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (10 10 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
                (10 10 (:TYPE-PRESCRIPTION NATP))
                (10 10 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                (10 10 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (10 10 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (10 10
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (10 10
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (10 10 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (10 10 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                (10 10
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (10 10
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (10 10 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                (10 10 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
                (10 10
                    (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD)))
(RTL::MOD-MULT
     (354 354
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (354 354
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (354 354
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (354 354
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (284 60 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (274 4 (:LINEAR MOD-BOUNDS-3))
     (272 8 (:LINEAR MOD-BOUNDS-2))
     (272 8 (:LINEAR MOD-BOUNDS-1))
     (260 60
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (260 60
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (215 9 (:REWRITE RTL::MOD-DOES-NOTHING))
     (176 10 (:REWRITE |(* y x)|))
     (176 6 (:REWRITE MOD-X-Y-=-X . 4))
     (176 6 (:REWRITE MOD-X-Y-=-X . 3))
     (171 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (171 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (171 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (171 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (168 2 (:REWRITE |(* x (+ y z))|))
     (128 4 (:LINEAR RTL::MOD-BND-2))
     (120 60 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (106 6 (:REWRITE MOD-ZERO . 3))
     (91 6 (:REWRITE MOD-ZERO . 4))
     (91 6 (:REWRITE MOD-X-Y-=-X . 2))
     (91 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (91 6
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (71 6 (:REWRITE CANCEL-MOD-+))
     (70 2 (:REWRITE |(* y (* x z))|))
     (68 2 (:REWRITE |(+ x (if a b c))|))
     (62 62 (:REWRITE THE-FLOOR-BELOW))
     (62 62 (:REWRITE THE-FLOOR-ABOVE))
     (62 62 (:REWRITE SIMPLIFY-SUMS-<))
     (62 62
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (62 62
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (62 62
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (62 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (62 62
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (62 62 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (62 62 (:REWRITE INTEGERP-<-CONSTANT))
     (62 62 (:REWRITE DEFAULT-LESS-THAN-2))
     (62 62 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (60 60 (:TYPE-PRESCRIPTION NATP))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (60 60
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (60 60 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (60 60 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (60 60
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (60 60
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (60 6 (:REWRITE DEFAULT-MOD-RATIO))
     (42 4 (:REWRITE |(+ y x)|))
     (38 38 (:REWRITE DEFAULT-TIMES-2))
     (38 38 (:REWRITE DEFAULT-TIMES-1))
     (35 11 (:REWRITE DEFAULT-PLUS-1))
     (30 6
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (30 6
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (30 6
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (28 2 (:REWRITE |(* a (/ a))|))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (27 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (27 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (27 27
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (27 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (27 27
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (27 27 (:REWRITE |(equal c (/ x))|))
     (27 27 (:REWRITE |(equal c (- x))|))
     (27 27 (:REWRITE |(equal (/ x) c)|))
     (27 27 (:REWRITE |(equal (/ x) (/ y))|))
     (27 27 (:REWRITE |(equal (- x) c)|))
     (27 27 (:REWRITE |(equal (- x) (- y))|))
     (27 27 (:REWRITE |(< 0 (/ x))|))
     (27 27 (:REWRITE |(< 0 (* x y))|))
     (27 27 (:REWRITE |(< (/ x) 0)|))
     (27 27 (:REWRITE |(< (* x y) 0)|))
     (27 11 (:REWRITE DEFAULT-PLUS-2))
     (26 6 (:REWRITE MOD-CANCEL-*-CONST))
     (26 2 (:REWRITE |(* x (if a b c))|))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (15 15 (:REWRITE DEFAULT-DIVIDE))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 2 (:REWRITE |(+ 0 x)|))
     (8 8 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (8 2 (:REWRITE RATIONALP-X))
     (6 6
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE DEFAULT-MOD-1))
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
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE |(* 1 x)|))
     (2 2 (:REWRITE |(* 0 x)|))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::MOD-FORCE
     (1663 1663
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1663 1663
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1663 1663
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1110 222 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1070 222 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1030 222
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1030 222
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (952 28 (:LINEAR MOD-BOUNDS-2))
     (668 21 (:REWRITE CANCEL-MOD-+))
     (667 21 (:REWRITE MOD-X-Y-=-X . 4))
     (667 21 (:REWRITE MOD-X-Y-=-X . 3))
     (648 21 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (648 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (648 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (615 615 (:REWRITE DEFAULT-TIMES-2))
     (615 615 (:REWRITE DEFAULT-TIMES-1))
     (600 21 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (575 310 (:REWRITE DEFAULT-PLUS-2))
     (496 21 (:REWRITE RTL::MOD-DOES-NOTHING))
     (444 222 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (434 14 (:LINEAR RTL::MOD-BND-2))
     (419 310 (:REWRITE DEFAULT-PLUS-1))
     (401 21 (:REWRITE MOD-ZERO . 3))
     (344 21 (:REWRITE MOD-ZERO . 4))
     (344 21 (:REWRITE MOD-X-Y-=-X . 2))
     (294 14 (:LINEAR MOD-BOUNDS-3))
     (291 283 (:REWRITE DEFAULT-LESS-THAN-2))
     (284 284
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (284 284
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (284 284
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (283 283 (:REWRITE THE-FLOOR-BELOW))
     (283 283 (:REWRITE THE-FLOOR-ABOVE))
     (283 283 (:REWRITE DEFAULT-LESS-THAN-1))
     (280 280
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (280 280
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (277 269
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (275 275 (:REWRITE INTEGERP-<-CONSTANT))
     (275 275 (:REWRITE CONSTANT-<-INTEGERP))
     (275 275
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (275 275
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (275 275
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (275 275
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (275 275 (:REWRITE |(< c (- x))|))
     (275 275
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (275 275
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (275 275
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (275 275
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (275 275 (:REWRITE |(< (/ x) (/ y))|))
     (275 275 (:REWRITE |(< (- x) c)|))
     (275 275 (:REWRITE |(< (- x) (- y))|))
     (257 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (256 16 (:REWRITE |(integerp (- x))|))
     (222 222
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (222 222 (:TYPE-PRESCRIPTION NATP))
     (222 222 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (222 222 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (222 222
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (222 222
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (222 222
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (222 222 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (222 222 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (222 222
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (215 215
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (210 21 (:REWRITE DEFAULT-MOD-RATIO))
     (160 16 (:REWRITE |(* (- x) y)|))
     (150 5
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (150 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (145 145 (:REWRITE |(< (* x y) 0)|))
     (143 143 (:REWRITE |(< (/ x) 0)|))
     (142 142
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (142 142
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (136 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (136 21
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (125 97 (:REWRITE |(equal (/ x) c)|))
     (121 5
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (120 120 (:REWRITE DEFAULT-DIVIDE))
     (118 118
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (118 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (117 117
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (105 21
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (105 21
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (105 21
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (97 97
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (97 97
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (97 97 (:REWRITE |(equal c (/ x))|))
     (97 97 (:REWRITE |(equal (/ x) (/ y))|))
     (97 97 (:REWRITE |(equal (- x) (- y))|))
     (97 21 (:REWRITE MOD-CANCEL-*-CONST))
     (95 95
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (95 95 (:REWRITE |(equal c (- x))|))
     (95 95 (:REWRITE |(equal (- x) c)|))
     (91 91 (:REWRITE INTEGERP-MINUS-X))
     (90 90 (:META META-INTEGERP-CORRECT))
     (88 22 (:REWRITE RATIONALP-X))
     (82 18 (:REWRITE DEFAULT-MINUS))
     (70 70
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (61 61 (:REWRITE |(< 0 (* x y))|))
     (59 59 (:REWRITE |(< 0 (/ x))|))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (29 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (27 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (26 26
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (22 22 (:REWRITE REDUCE-RATIONALP-+))
     (22 22 (:REWRITE REDUCE-RATIONALP-*))
     (22 22 (:REWRITE RATIONALP-MINUS-X))
     (22 22 (:META META-RATIONALP-CORRECT))
     (21 21
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (21 21 (:REWRITE DEFAULT-MOD-2))
     (21 21 (:REWRITE DEFAULT-MOD-1))
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
     (20 20 (:REWRITE |(< (+ c/d x) y)|))
     (19 19 (:REWRITE |(< (+ (- c) x) y)|))
     (17 17 (:REWRITE |(< x (+ c/d y))|))
     (17 17 (:REWRITE |(- (* c x))|))
     (16 16 (:REWRITE |arith (* c (* d x))|))
     (16 16 (:REWRITE |(< y (+ (- c) x))|))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
     (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (8 8 (:REWRITE |arith (- (* c x))|))
     (8 8 (:REWRITE |arith (* (- x) y)|))
     (7 7 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (5 5 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|)))
(RTL::MOD-BND-3
     (1195 239 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1172 1172
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1172 1172
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1172 1172
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1087 239 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1015 239
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1015 239
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (478 239 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (239 239
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (239 239 (:TYPE-PRESCRIPTION NATP))
     (239 239 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (239 239 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (239 239
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (239 239
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (239 239
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (239 239
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (239 239 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (239 239 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (239 239
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (223 91 (:REWRITE DEFAULT-LESS-THAN-1))
     (221 85
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (221 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (210 6 (:REWRITE MOD-X-Y-=-X . 4))
     (210 6 (:REWRITE MOD-X-Y-=-X . 3))
     (206 144 (:REWRITE DEFAULT-PLUS-1))
     (204 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (204 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (204 6 (:LINEAR MOD-BOUNDS-2))
     (196 40 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (189 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (172 172 (:REWRITE DEFAULT-TIMES-2))
     (172 172 (:REWRITE DEFAULT-TIMES-1))
     (156 6 (:REWRITE RTL::MOD-DOES-NOTHING))
     (146 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (146 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (133 44
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (126 6 (:REWRITE MOD-ZERO . 3))
     (124 4 (:LINEAR RTL::MOD-BND-2))
     (118 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (116 116
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (116 116
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (116 116
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (116 116
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (108 6 (:REWRITE MOD-ZERO . 4))
     (108 6 (:REWRITE MOD-X-Y-=-X . 2))
     (108 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (108 6
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (95 91 (:REWRITE DEFAULT-LESS-THAN-2))
     (91 91 (:REWRITE THE-FLOOR-BELOW))
     (91 91 (:REWRITE THE-FLOOR-ABOVE))
     (89 89
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (89 89
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (89 89
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (89 89
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (89 89 (:REWRITE INTEGERP-<-CONSTANT))
     (89 89 (:REWRITE CONSTANT-<-INTEGERP))
     (89 89
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (89 89
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (89 89
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (89 89
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (89 89 (:REWRITE |(< c (- x))|))
     (89 89
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (89 89
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (89 89
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (89 89
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (89 89 (:REWRITE |(< (/ x) (/ y))|))
     (89 89 (:REWRITE |(< (- x) c)|))
     (89 89 (:REWRITE |(< (- x) (- y))|))
     (88 6 (:LINEAR MOD-BOUNDS-1))
     (84 6 (:REWRITE CANCEL-MOD-+))
     (73 73
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (68 17 (:REWRITE RATIONALP-X))
     (63 7 (:REWRITE ACL2-NUMBERP-X))
     (63 3 (:LINEAR MOD-BOUNDS-3))
     (60 6 (:REWRITE DEFAULT-MOD-RATIO))
     (59 59
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (59 45 (:REWRITE |(equal (/ x) c)|))
     (45 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (45 45 (:REWRITE |(equal c (/ x))|))
     (45 45 (:REWRITE |(equal (/ x) (/ y))|))
     (45 45 (:REWRITE |(equal (- x) (- y))|))
     (44 44
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (44 44 (:REWRITE |(equal c (- x))|))
     (44 44 (:REWRITE |(equal (- x) c)|))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (33 33 (:REWRITE REDUCE-INTEGERP-+))
     (33 33 (:REWRITE INTEGERP-MINUS-X))
     (33 33 (:META META-INTEGERP-CORRECT))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (32 32 (:REWRITE |(< (/ x) 0)|))
     (32 32 (:REWRITE |(< (* x y) 0)|))
     (30 6
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (30 6 (:REWRITE MOD-CANCEL-*-CONST))
     (30 6
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (30 6
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (28 28 (:REWRITE DEFAULT-DIVIDE))
     (27 27 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (27 27
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (27 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (24 24 (:REWRITE |(< 0 (/ x))|))
     (24 24 (:REWRITE |(< 0 (* x y))|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17 (:META META-RATIONALP-CORRECT))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (14 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|))
     (10 10 (:REWRITE |(+ c (+ d x))|))
     (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE DEFAULT-MOD-1))
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
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(/ (/ x))|))
     (1 1 (:REWRITE |(- (* c x))|)))
(RTL::MOD-SUM
     (96206 97 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (40597 527 (:REWRITE RTL::MOD-DOES-NOTHING))
     (18195 8889 (:REWRITE DEFAULT-TIMES-2))
     (17878 574 (:LINEAR MOD-BOUNDS-1))
     (17526 445 (:REWRITE MOD-X-Y-=-X . 4))
     (17351 445 (:REWRITE MOD-X-Y-=-X . 3))
     (15323 8889 (:REWRITE DEFAULT-TIMES-1))
     (15080 773 (:REWRITE RATIONALP-X))
     (14570 6434 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (14419 14419
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (14419 14419
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (14419 14419
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (14279 2168 (:REWRITE DEFAULT-PLUS-2))
     (14237 6434 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (13514 453 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (13019 453 (:REWRITE MOD-ZERO . 4))
     (8301 2168 (:REWRITE DEFAULT-PLUS-1))
     (8165 442 (:REWRITE CANCEL-MOD-+))
     (7906 6434
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (7904 6432
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (7904 6432
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (7463 453 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (7457 453 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (6554 6434
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6434 6434 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6434 6434 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6434 6434
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6431 6431
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6403 6403 (:TYPE-PRESCRIPTION NATP))
     (5183 18 (:REWRITE |(< (if a b c) x)|))
     (5028 5028
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4859 445 (:REWRITE MOD-X-Y-=-X . 2))
     (4859 445
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (4805 3096
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4697 1315
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4637 3096
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3862 3096 (:REWRITE SIMPLIFY-SUMS-<))
     (3369 2778 (:REWRITE DEFAULT-DIVIDE))
     (3156 3156 (:REWRITE THE-FLOOR-BELOW))
     (3156 3156 (:REWRITE THE-FLOOR-ABOVE))
     (3107 3107
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3107 3107
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3107 3107
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3107 3107 (:REWRITE INTEGERP-<-CONSTANT))
     (3107 3107 (:REWRITE CONSTANT-<-INTEGERP))
     (3107 3107
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3107 3107
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3107 3107
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3107 3107
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3107 3107 (:REWRITE |(< c (- x))|))
     (3107 3107
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3107 3107
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3107 3107
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3107 3107
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3107 3107 (:REWRITE |(< (/ x) (/ y))|))
     (3107 3107 (:REWRITE |(< (- x) c)|))
     (3107 3107 (:REWRITE |(< (- x) (- y))|))
     (2967 442 (:REWRITE MOD-CANCEL-*-CONST))
     (2727 2727
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2296 267 (:REWRITE |(integerp (- x))|))
     (1733 442
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1733 442
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1733 442
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (1700 270 (:REWRITE |(* (- x) y)|))
     (1684 442
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1684 442
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1684 442
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1588 1563 (:REWRITE INTEGERP-MINUS-X))
     (1563 1563 (:REWRITE REDUCE-INTEGERP-+))
     (1563 1563 (:META META-INTEGERP-CORRECT))
     (1420 1420
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1381 1318 (:REWRITE |(equal (/ x) (/ y))|))
     (1318 1318
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1318 1318
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1318 1318 (:REWRITE |(equal c (/ x))|))
     (1318 1318 (:REWRITE |(equal (- x) (- y))|))
     (1315 1315
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1315 1315 (:REWRITE |(equal c (- x))|))
     (1315 1315 (:REWRITE |(equal (- x) c)|))
     (1253 1253
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1253 1253
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1253 1253 (:REWRITE |(< 0 (/ x))|))
     (1253 1253 (:REWRITE |(< 0 (* x y))|))
     (1175 1175
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1175 1175 (:REWRITE |(< (/ x) 0)|))
     (1175 1175 (:REWRITE |(< (* x y) 0)|))
     (1174 1174
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1174 1174
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1098 509 (:REWRITE DEFAULT-MOD-1))
     (939 51
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (912 27 (:REWRITE |(+ (+ x y) z)|))
     (890 202 (:REWRITE ACL2-NUMBERP-X))
     (780 2
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (778 778
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (778 778
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (778 778
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (704 704 (:REWRITE RATIONALP-MINUS-X))
     (688 688 (:META META-RATIONALP-CORRECT))
     (610 51
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (579 51
          (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (560 50 (:REWRITE MOD-ZERO . 1))
     (442 442 (:REWRITE |(mod x (- y))| . 3))
     (442 442 (:REWRITE |(mod x (- y))| . 2))
     (442 442 (:REWRITE |(mod x (- y))| . 1))
     (442 442 (:REWRITE |(mod (- x) y)| . 3))
     (442 442 (:REWRITE |(mod (- x) y)| . 2))
     (442 442 (:REWRITE |(mod (- x) y)| . 1))
     (441 87
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (436 327 (:REWRITE DEFAULT-MINUS))
     (427 21 (:REWRITE MOD-NONNEGATIVE))
     (389 146 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (303 50 (:REWRITE MOD-ZERO . 2))
     (299 299 (:LINEAR RTL::MOD-BND-3))
     (273 273 (:REWRITE |(- (* c x))|))
     (246 22 (:REWRITE MOD-NEGATIVE . 3))
     (204 22 (:REWRITE MOD-NEGATIVE . 2))
     (195 195 (:REWRITE |(equal (+ (- c) x) y)|))
     (194 194 (:REWRITE |(< (+ c/d x) y)|))
     (194 194 (:REWRITE |(< (+ (- c) x) y)|))
     (159 33 (:REWRITE |(equal x (/ y))|))
     (146 146 (:REWRITE |(+ c (+ d x))|))
     (133 133
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (128 128 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (112 112 (:REWRITE |(< y (+ (- c) x))|))
     (112 112 (:REWRITE |(< x (+ c/d y))|))
     (96 33 (:REWRITE |(not (equal x (/ y)))|))
     (69 69 (:REWRITE INTEGERP-/))
     (67 67 (:REWRITE FOLD-CONSTS-IN-+))
     (67 1 (:REWRITE |(- (+ x y))|))
     (55 7 (:REWRITE |(mod (mod x y) z)| . 3))
     (51 51
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (51 51
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (36 8 (:REWRITE MOD-POSITIVE . 3))
     (15 7 (:REWRITE |(mod (mod x y) z)| . 1))
     (8 8 (:REWRITE MOD-POSITIVE . 2))
     (8 2 (:REWRITE |(+ x x)|))
     (7 7 (:REWRITE MOD-NONPOSITIVE))
     (7 7 (:REWRITE |(mod (mod x y) z)| . 2)))
(RTL::MOD-DIFF
     (102170 1449 (:REWRITE RTL::MOD-DOES-NOTHING))
     (59759 79
            (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (57254 10090 (:REWRITE DEFAULT-PLUS-2))
     (56760 1333 (:REWRITE MOD-X-Y-=-X . 4))
     (56475 1333 (:REWRITE MOD-X-Y-=-X . 3))
     (55564 79
            (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (41895 1350 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (39328 1350 (:REWRITE MOD-ZERO . 4))
     (37288 22817 (:REWRITE DEFAULT-TIMES-2))
     (36460 1474 (:LINEAR MOD-BOUNDS-1))
     (36399 16417
            (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (34772 10090 (:REWRITE DEFAULT-PLUS-1))
     (31650 22817 (:REWRITE DEFAULT-TIMES-1))
     (30125 16417 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (24707 24707
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (24707 24707
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (24707 24707
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (21898 1122 (:REWRITE RATIONALP-X))
     (20241 16417
            (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (20188 16364
            (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (20188 16364
            (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (16969 16417
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (16744 1350 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (16605 1350 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (16425 16417 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (16417 16417 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (16417 16417
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (16386 16386 (:TYPE-PRESCRIPTION NATP))
     (16181 16181
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (15507 8714
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11541 11541
            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11483 18 (:REWRITE |(< (if a b c) x)|))
     (11012 8815 (:REWRITE |(< c (- x))|))
     (10749 1333 (:REWRITE MOD-X-Y-=-X . 2))
     (10695 2836
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10332 8757 (:REWRITE |(< (- x) c)|))
     (10179 4250 (:REWRITE DEFAULT-MINUS))
     (10049 1330
            (:REWRITE |(mod (+ x (mod a b)) y)|))
     (9748 8815 (:REWRITE |(< (- x) (- y))|))
     (8878 8878 (:REWRITE THE-FLOOR-BELOW))
     (8878 8878 (:REWRITE THE-FLOOR-ABOVE))
     (8815 8815
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8815 8815
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8815 8815
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (8815 8815
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8815 8815
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (8815 8815
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (8815 8815
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (8815 8815
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (8815 8815
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (8815 8815
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (8815 8815
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (8815 8815 (:REWRITE |(< (/ x) (/ y))|))
     (8727 8727 (:REWRITE INTEGERP-<-CONSTANT))
     (8727 8727 (:REWRITE CONSTANT-<-INTEGERP))
     (7733 7029 (:REWRITE DEFAULT-DIVIDE))
     (6964 6964
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (6309 1297 (:REWRITE MOD-CANCEL-*-CONST))
     (5818 1294 (:REWRITE |(mod (- x) y)| . 3))
     (4443 1297
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4379 1131 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4256 64 (:REWRITE |(* x (if a b c))|))
     (4052 1242
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4052 1242
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (3927 3927 (:REWRITE |(- (* c x))|))
     (3827 2866 (:REWRITE |(equal (- x) c)|))
     (3692 2718 (:REWRITE INTEGERP-MINUS-X))
     (3527 1297
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (3272 3272
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3168 3168 (:REWRITE |(< 0 (/ x))|))
     (3168 3168 (:REWRITE |(< 0 (* x y))|))
     (2930 1242
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (2930 1242
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (2928 2928
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2928 2928
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2895 2869
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2883 2866 (:REWRITE |(equal c (- x))|))
     (2881 2867 (:REWRITE |(equal (/ x) c)|))
     (2868 2868
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2868 2868 (:REWRITE |(equal (/ x) (/ y))|))
     (2867 2867 (:REWRITE |(equal c (/ x))|))
     (2836 2836
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2821 2821 (:REWRITE |(< (/ x) 0)|))
     (2821 2821 (:REWRITE |(< (* x y) 0)|))
     (2717 2717 (:META META-INTEGERP-CORRECT))
     (2588 2588
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2588 2588
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2357 2357
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2218 1424 (:REWRITE DEFAULT-MOD-1))
     (1728 994 (:REWRITE RATIONALP-MINUS-X))
     (1727 79
           (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (1707 1707
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1707 1707
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1707 1707
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1294 1294 (:REWRITE |(mod x (- y))| . 3))
     (1294 1294 (:REWRITE |(mod x (- y))| . 2))
     (1294 1294 (:REWRITE |(mod x (- y))| . 1))
     (1270 1270 (:REWRITE |(mod (- x) y)| . 2))
     (1158 262 (:REWRITE ACL2-NUMBERP-X))
     (1070 55 (:REWRITE MOD-NONNEGATIVE))
     (968 968 (:META META-RATIONALP-CORRECT))
     (965 4
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (906 58 (:REWRITE MOD-NEGATIVE . 3))
     (802 79
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (761 761 (:LINEAR RTL::MOD-BND-3))
     (740 59 (:REWRITE MOD-ZERO . 1))
     (513 58 (:REWRITE MOD-NEGATIVE . 2))
     (476 476 (:REWRITE |(< y (+ (- c) x))|))
     (476 476 (:REWRITE |(< x (+ c/d y))|))
     (462 462 (:REWRITE |(< (+ c/d x) y)|))
     (462 462 (:REWRITE |(< (+ (- c) x) y)|))
     (370 91
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (366 366 (:REWRITE |(+ c (+ d x))|))
     (356 356 (:REWRITE |(equal (+ (- c) x) y)|))
     (315 59 (:REWRITE MOD-ZERO . 2))
     (247 79
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (237 237
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (203 203 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (161 161 (:REWRITE FOLD-CONSTS-IN-+))
     (131 19 (:REWRITE |(mod (mod x y) z)| . 3))
     (98 98 (:REWRITE INTEGERP-/))
     (92 1 (:REWRITE |(- (+ x y))|))
     (35 23 (:REWRITE MOD-POSITIVE . 3))
     (31 31 (:REWRITE |(not (equal x (/ y)))|))
     (31 31 (:REWRITE |(equal x (/ y))|))
     (28 7 (:REWRITE |(+ x x)|))
     (23 23 (:REWRITE MOD-POSITIVE . 2))
     (20 20 (:REWRITE MOD-NONPOSITIVE))
     (19 19 (:REWRITE |(mod (mod x y) z)| . 2))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1 1 (:TYPE-PRESCRIPTION ABS))
     (1 1 (:REWRITE |(equal (* x y) 0)|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(RTL::MOD-OF-MOD
     (34990 828
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (34977 61 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (28372 232 (:REWRITE RTL::MOD-DOES-NOTHING))
     (25247 10433 (:REWRITE DEFAULT-TIMES-2))
     (25178 248 (:LINEAR MOD-BOUNDS-1))
     (14154 10433 (:REWRITE DEFAULT-TIMES-1))
     (13852 558 (:REWRITE RATIONALP-X))
     (11363 2255 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (11331 2255 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (10712 10712
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (10712 10712
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (10712 10712
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (10556 124 (:LINEAR RTL::MOD-BND-2))
     (9924 248 (:LINEAR MOD-BOUNDS-2))
     (9662 182 (:REWRITE MOD-X-Y-=-X . 4))
     (8908 182 (:REWRITE MOD-X-Y-=-X . 3))
     (8778 6 (:REWRITE |(< (if a b c) x)|))
     (8549 184 (:REWRITE MOD-ZERO . 4))
     (7603 184 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (7546 184 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (5724 124 (:LINEAR MOD-BOUNDS-3))
     (5601 5601
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5601 5601
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5601 5601
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5568 5568
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5517 179
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (5289 179
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (5259 5259 (:REWRITE DEFAULT-DIVIDE))
     (4592 2255 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (4522 184 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (4522 184 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (3969 3969
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3689 179 (:REWRITE MOD-CANCEL-*-CONST))
     (3547 894 (:REWRITE DEFAULT-PLUS-2))
     (3534 179 (:REWRITE CANCEL-MOD-+))
     (2965 1297 (:REWRITE DEFAULT-LESS-THAN-1))
     (2951 2255
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2951 2255
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2918 798 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2895 179
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2892 176
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (2892 176
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2434 828
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2359 2255 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (2359 2255 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2359 2255
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2359 2255
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (2359 2255
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2358 2254
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2358 2254
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2237 2237 (:TYPE-PRESCRIPTION NATP))
     (2211 2107 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (2174 1190 (:META META-INTEGERP-CORRECT))
     (2079 116 (:REWRITE MOD-X-I*J))
     (1708 1272
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1681 1272
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1637 894 (:REWRITE DEFAULT-PLUS-1))
     (1493 179
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1382 1297 (:REWRITE DEFAULT-LESS-THAN-2))
     (1306 1306 (:REWRITE |(* c (* d x))|))
     (1297 1297 (:REWRITE THE-FLOOR-BELOW))
     (1297 1297 (:REWRITE THE-FLOOR-ABOVE))
     (1273 1273
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1273 1273
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1273 1273
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1273 1273
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1273 1273 (:REWRITE INTEGERP-<-CONSTANT))
     (1273 1273 (:REWRITE CONSTANT-<-INTEGERP))
     (1273 1273
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1273 1273
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1273 1273
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1273 1273
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1273 1273 (:REWRITE |(< c (- x))|))
     (1273 1273
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1273 1273
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1273 1273
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1273 1273
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1273 1273 (:REWRITE |(< (/ x) (/ y))|))
     (1273 1273 (:REWRITE |(< (- x) c)|))
     (1273 1273 (:REWRITE |(< (- x) (- y))|))
     (1197 165 (:REWRITE ACL2-NUMBERP-X))
     (1190 1190 (:REWRITE REDUCE-INTEGERP-+))
     (1190 1190 (:REWRITE INTEGERP-MINUS-X))
     (1134 454
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (1134 454
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (1134 454
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (1130 176
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1130 176
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (926 522 (:META META-RATIONALP-CORRECT))
     (828 828
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (828 828
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (828 828
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (828 828 (:REWRITE |(equal c (/ x))|))
     (828 828 (:REWRITE |(equal c (- x))|))
     (828 828 (:REWRITE |(equal (/ x) c)|))
     (828 828 (:REWRITE |(equal (/ x) (/ y))|))
     (828 828 (:REWRITE |(equal (- x) c)|))
     (828 828 (:REWRITE |(equal (- x) (- y))|))
     (736 736
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (730 722
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (730 722
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (730 722
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (728 116 (:REWRITE MOD-X-I*J-V2))
     (722 722
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3F))
     (722 722
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2F))
     (722 722
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1F))
     (707 707
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (707 707
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (707 707 (:REWRITE |(< 0 (/ x))|))
     (707 707 (:REWRITE |(< 0 (* x y))|))
     (688 43 (:REWRITE |(integerp (- x))|))
     (604 4
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (559 43 (:REWRITE |(* (- x) y)|))
     (558 558 (:REWRITE RATIONALP-MINUS-X))
     (454 454
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
     (454 454
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (454 454
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (454 454
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (431 11 (:REWRITE MOD-ZERO . 1))
     (325 5 (:REWRITE MOD-NONNEGATIVE))
     (325 5 (:REWRITE MOD-NEGATIVE . 3))
     (315 315
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (314 314 (:REWRITE |(< (/ x) 0)|))
     (314 314 (:REWRITE |(< (* x y) 0)|))
     (313 313
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (313 313
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (272 4
          (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
     (258 56
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (246 246 (:REWRITE INTEGERP-/))
     (240 68 (:REWRITE DEFAULT-MINUS))
     (235 235 (:REWRITE |(equal (* x y) 0)|))
     (231 231 (:REWRITE DEFAULT-MOD-2))
     (229 229
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (219 11 (:REWRITE MOD-ZERO . 2))
     (176 176 (:REWRITE |(mod x (- y))| . 3))
     (176 176 (:REWRITE |(mod x (- y))| . 2))
     (176 176 (:REWRITE |(mod x (- y))| . 1))
     (176 176 (:REWRITE |(mod (- x) y)| . 3))
     (176 176 (:REWRITE |(mod (- x) y)| . 2))
     (176 176 (:REWRITE |(mod (- x) y)| . 1))
     (131 99 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (124 124 (:LINEAR RTL::MOD-BND-3))
     (96 12 (:REWRITE RTL::RATIONALP-MOD))
     (86 86 (:REWRITE |(equal (+ (- c) x) y)|))
     (72 12 (:REWRITE RATIONALP-MOD))
     (68 68 (:REWRITE |(not (equal x (/ y)))|))
     (68 68 (:REWRITE |(equal x (/ y))|))
     (64 8 (:REWRITE INTP-3))
     (56 56 (:REWRITE |(- (* c x))|))
     (52 12 (:REWRITE INTEGERP-MOD-2))
     (52 12 (:REWRITE INTEGERP-MOD-1))
     (52 12 (:REWRITE RTL::INTEGERP-MOD))
     (50 50 (:REWRITE |(+ c (+ d x))|))
     (48 48
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (33 5 (:REWRITE MOD-NEGATIVE . 2))
     (32 4 (:REWRITE INTP-1))
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
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (28 28 (:TYPE-PRESCRIPTION INTP-*))
     (24 24 (:TYPE-PRESCRIPTION FIX))
     (15 3 (:REWRITE MOD-POSITIVE . 3))
     (15 3 (:REWRITE MOD-NONPOSITIVE))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (8 8 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
     (5 5 (:REWRITE MOD-NEGATIVE . 1))
     (4 4
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (4 4
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (4 4
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (4 4
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (3 3 (:REWRITE MOD-POSITIVE . 2))
     (3 3 (:REWRITE MOD-POSITIVE . 1))
     (3 3 (:REWRITE |(mod (mod x y) z)| . 3))
     (3 3 (:REWRITE |(mod (mod x y) z)| . 2))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|)))
(RTL::MOD-OF-MOD-COR-R
 (189510 27 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (121269 154 (:LINEAR MOD-BOUNDS-1))
 (93242 207
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (75306 27 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (33870 210 (:REWRITE CANCEL-MOD-+))
 (32915 77 (:LINEAR RTL::MOD-BND-2))
 (31121 213 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (26492 10 (:REWRITE |(< (if a b c) x)|))
 (21304
  21304
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21304
      21304
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21304
     21304
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21304 21304
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21304 21304
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (19500 213 (:REWRITE MOD-ZERO . 3))
 (17243 1178 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (16686 213 (:REWRITE MOD-X-Y-=-X . 3))
 (13870 1233 (:REWRITE DEFAULT-TIMES-2))
 (13775 784
        (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (13068 213 (:REWRITE MOD-X-Y-=-X . 4))
 (12509 1178
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (12509 1178
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (11669 213 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (11453 213 (:REWRITE MOD-ZERO . 4))
 (10806 198 (:REWRITE |(integerp (- x))|))
 (9999 3718 (:REWRITE DEFAULT-LESS-THAN-1))
 (9512 392 (:LINEAR EXPT->=-1-ONE))
 (9512 392 (:LINEAR EXPT-<=-1-TWO))
 (8688 784
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8494 3695
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8414 1178 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (8390 839 (:REWRITE DEFAULT-DIVIDE))
 (8319 3695 (:REWRITE SIMPLIFY-SUMS-<))
 (8296 392 (:LINEAR EXPT->=-1-TWO))
 (8296 392 (:LINEAR EXPT-<=-1-ONE))
 (8080 226 (:REWRITE RATIONALP-X))
 (7992 392 (:LINEAR EXPT-X->=-X))
 (7992 392 (:LINEAR EXPT-X->-X))
 (7992 392 (:LINEAR EXPT->-1-ONE))
 (7992 392 (:LINEAR EXPT-<-1-TWO))
 (7935 3718 (:REWRITE DEFAULT-LESS-THAN-2))
 (7710 154 (:LINEAR MOD-BOUNDS-2))
 (7605 7605
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7605 7605
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7605 7605
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7605 7605
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (7605 7605
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7591 77 (:LINEAR MOD-BOUNDS-3))
 (7456 213
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (6690 198 (:REWRITE |(* (- x) y)|))
 (6522 3695
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6338 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (6338 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (5539 213 (:REWRITE MOD-X-Y-=-X . 2))
 (5462 213 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (5462 213 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4862 1233 (:REWRITE DEFAULT-TIMES-1))
 (4837 1045 (:REWRITE DEFAULT-MINUS))
 (3718 3718 (:REWRITE THE-FLOOR-BELOW))
 (3718 3718 (:REWRITE THE-FLOOR-ABOVE))
 (3695 3695
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3695 3695
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3695 3695
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3695 3695
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3695 3695 (:REWRITE INTEGERP-<-CONSTANT))
 (3695 3695 (:REWRITE CONSTANT-<-INTEGERP))
 (3695 3695
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3695 3695
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3695 3695
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3695 3695
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3695 3695 (:REWRITE |(< c (- x))|))
 (3695 3695
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3695 3695
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3695 3695
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3695 3695
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3695 3695 (:REWRITE |(< (/ x) (/ y))|))
 (3695 3695 (:REWRITE |(< (- x) c)|))
 (3695 3695 (:REWRITE |(< (- x) (- y))|))
 (3453 210
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3453 210
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (3453 210
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3288 210 (:REWRITE MOD-CANCEL-*-CONST))
 (2660 266 (:REWRITE DEFAULT-MOD-2))
 (2656 207
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2544 1178 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (2234 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (2234 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1989 1989
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1883 199 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1644 1644 (:REWRITE DEFAULT-EXPT-2))
 (1644 1644 (:REWRITE DEFAULT-EXPT-1))
 (1644 1644 (:REWRITE |(expt 1/c n)|))
 (1644 1644 (:REWRITE |(expt (- x) n)|))
 (1486 125 (:REWRITE DEFAULT-PLUS-2))
 (1370 1178 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (1370 1178 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1370 1178
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1370 1178
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1370 1178
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1370 1178
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1370 1178
       (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (1370 1178
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (1178 1178 (:TYPE-PRESCRIPTION NATP))
 (986 138 (:REWRITE ACL2-NUMBERP-X))
 (784 784
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (784 784
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (645 645
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (645 645
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (645 645 (:REWRITE REDUCE-INTEGERP-+))
 (645 645 (:REWRITE INTEGERP-MINUS-X))
 (645 645 (:REWRITE |(< (/ x) 0)|))
 (645 645 (:REWRITE |(< (* x y) 0)|))
 (645 645 (:META META-INTEGERP-CORRECT))
 (607 415 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (478 478
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (478 478
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (478 478 (:REWRITE |(< 0 (/ x))|))
 (478 478 (:REWRITE |(< 0 (* x y))|))
 (392 392 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (392 392 (:LINEAR EXPT-LINEAR-UPPER-<))
 (392 392 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (392 392 (:LINEAR EXPT-LINEAR-LOWER-<))
 (392 392 (:LINEAR EXPT->-1-TWO))
 (392 392 (:LINEAR EXPT-<-1-ONE))
 (356 6 (:REWRITE MOD-NEGATIVE . 3))
 (354 43 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (324 4 (:REWRITE MOD-NONNEGATIVE))
 (285 210
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (285 210
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (285 210
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (226 226 (:REWRITE RATIONALP-MINUS-X))
 (225 207 (:REWRITE |(equal (- x) (- y))|))
 (214 214 (:REWRITE REDUCE-RATIONALP-+))
 (214 214 (:META META-RATIONALP-CORRECT))
 (210 210 (:REWRITE |(mod x (- y))| . 3))
 (210 210 (:REWRITE |(mod x (- y))| . 2))
 (210 210 (:REWRITE |(mod x (- y))| . 1))
 (210 210 (:REWRITE |(mod (- x) y)| . 3))
 (210 210 (:REWRITE |(mod (- x) y)| . 2))
 (210 210 (:REWRITE |(mod (- x) y)| . 1))
 (207 207
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (207 207
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (207 207
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (207 207 (:REWRITE |(equal c (/ x))|))
 (207 207 (:REWRITE |(equal c (- x))|))
 (207 207 (:REWRITE |(equal (/ x) c)|))
 (207 207 (:REWRITE |(equal (/ x) (/ y))|))
 (207 207 (:REWRITE |(equal (- x) c)|))
 (198 198 (:REWRITE |(- (* c x))|))
 (198 27
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (181 181
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (77 77 (:LINEAR RTL::MOD-BND-3))
 (72 3 (:REWRITE MOD-POSITIVE . 3))
 (60 6 (:REWRITE MOD-NEGATIVE . 2))
 (57 3 (:REWRITE MOD-NONPOSITIVE))
 (51 3 (:REWRITE MOD-ZERO . 1))
 (36 4 (:REWRITE RTL::RATIONALP-MOD))
 (33 33
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 3 (:REWRITE MOD-POSITIVE . 2))
 (27 3 (:REWRITE MOD-ZERO . 2))
 (24 24 (:REWRITE |(equal (+ (- c) x) y)|))
 (24 4 (:REWRITE RATIONALP-MOD))
 (18 18
     (:REWRITE |(* (expt c m) (expt d n))|))
 (16 4 (:REWRITE INTEGERP-MOD-2))
 (16 4 (:REWRITE INTEGERP-MOD-1))
 (16 4 (:REWRITE RTL::INTEGERP-MOD))
 (6 6
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (6 6 (:REWRITE MOD-NEGATIVE . 1))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE MOD-POSITIVE . 1)))
(RTL::MOD-OF-MOD-COR
 (184574 27 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (122401 154 (:LINEAR MOD-BOUNDS-1))
 (91415 207
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (71018 27 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (34524 213 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (33870 210 (:REWRITE CANCEL-MOD-+))
 (32771 77 (:LINEAR RTL::MOD-BND-2))
 (25290 10 (:REWRITE |(< (if a b c) x)|))
 (21541
  21541
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21541
      21541
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21541
     21541
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21541 21541
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21541 21541
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (19511 213 (:REWRITE MOD-ZERO . 3))
 (17546 1195 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (16767 213 (:REWRITE MOD-X-Y-=-X . 3))
 (14438 1335 (:REWRITE DEFAULT-TIMES-2))
 (13871 880
        (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (13083 213 (:REWRITE MOD-X-Y-=-X . 4))
 (12710 1195
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (12710 1195
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (11673 213 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (11468 213 (:REWRITE MOD-ZERO . 4))
 (10806 198 (:REWRITE |(integerp (- x))|))
 (9560 440 (:LINEAR EXPT->=-1-ONE))
 (9560 440 (:LINEAR EXPT-<=-1-TWO))
 (9256 440 (:LINEAR EXPT->-1-ONE))
 (9256 440 (:LINEAR EXPT-<-1-TWO))
 (8537 1195 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (8390 839 (:REWRITE DEFAULT-DIVIDE))
 (8193 2805 (:REWRITE DEFAULT-LESS-THAN-1))
 (8156 226 (:REWRITE RATIONALP-X))
 (8040 440 (:LINEAR EXPT-X->=-X))
 (8040 440 (:LINEAR EXPT-X->-X))
 (7758 154 (:LINEAR MOD-BOUNDS-2))
 (7669 7669
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7669 7669
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7669 7669
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7669 7669
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (7669 7669
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7605 77 (:LINEAR MOD-BOUNDS-3))
 (7593 2782
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7458 213
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (7415 2782 (:REWRITE SIMPLIFY-SUMS-<))
 (7023 2805 (:REWRITE DEFAULT-LESS-THAN-2))
 (6690 198 (:REWRITE |(* (- x) y)|))
 (6338 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (6338 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (5619 2782
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5541 213 (:REWRITE MOD-X-Y-=-X . 2))
 (5463 213 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (5463 213 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (5043 1335 (:REWRITE DEFAULT-TIMES-1))
 (4855 1063 (:REWRITE DEFAULT-MINUS))
 (3453 210
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3453 210
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (3453 210
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3288 210 (:REWRITE MOD-CANCEL-*-CONST))
 (2805 2805 (:REWRITE THE-FLOOR-BELOW))
 (2805 2805 (:REWRITE THE-FLOOR-ABOVE))
 (2782 2782
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2782 2782
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2782 2782
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2782 2782
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2782 2782 (:REWRITE INTEGERP-<-CONSTANT))
 (2782 2782 (:REWRITE CONSTANT-<-INTEGERP))
 (2782 2782
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2782 2782
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2782 2782
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2782 2782
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2782 2782 (:REWRITE |(< c (- x))|))
 (2782 2782
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2782 2782
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2782 2782
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2782 2782
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2782 2782 (:REWRITE |(< (/ x) (/ y))|))
 (2782 2782 (:REWRITE |(< (- x) c)|))
 (2782 2782 (:REWRITE |(< (- x) (- y))|))
 (2686 443 (:REWRITE ODD-EXPT-THM))
 (2685 207
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2660 266 (:REWRITE DEFAULT-MOD-2))
 (2582 1195 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (2234 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (2234 2018
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1903 199 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1680 1680 (:REWRITE DEFAULT-EXPT-2))
 (1680 1680 (:REWRITE DEFAULT-EXPT-1))
 (1680 1680 (:REWRITE |(expt 1/c n)|))
 (1680 1680 (:REWRITE |(expt (- x) n)|))
 (1595 221 (:REWRITE DEFAULT-PLUS-2))
 (1391 1195 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (1391 1195 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1391 1195
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1391 1195
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1391 1195
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1391 1195
       (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (1391 1195
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1391 1195
       (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (1391 1195
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (1195 1195 (:TYPE-PRESCRIPTION NATP))
 (1076 1076
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (986 138 (:REWRITE ACL2-NUMBERP-X))
 (949 949
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (949 949
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (949 949 (:REWRITE |(< (/ x) 0)|))
 (949 949 (:REWRITE |(< (* x y) 0)|))
 (880 880
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (880 880
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (880 880
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (876 876 (:REWRITE REDUCE-INTEGERP-+))
 (876 876 (:REWRITE INTEGERP-MINUS-X))
 (876 876 (:META META-INTEGERP-CORRECT))
 (781 781
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (781 781
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (781 781 (:REWRITE |(< 0 (/ x))|))
 (781 781 (:REWRITE |(< 0 (* x y))|))
 (613 417 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (576 48 (:REWRITE |(* x (expt x n))|))
 (480 48 (:REWRITE |(* c (expt d n))|))
 (440 440 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (440 440 (:LINEAR EXPT-LINEAR-UPPER-<))
 (440 440 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (440 440 (:LINEAR EXPT-LINEAR-LOWER-<))
 (440 440 (:LINEAR EXPT->=-1-TWO))
 (440 440 (:LINEAR EXPT->-1-TWO))
 (440 440 (:LINEAR EXPT-<=-1-ONE))
 (440 440 (:LINEAR EXPT-<-1-ONE))
 (403 91 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (356 6 (:REWRITE MOD-NEGATIVE . 3))
 (324 4 (:REWRITE MOD-NONNEGATIVE))
 (285 210
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (285 210
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (285 210
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (226 226 (:REWRITE RATIONALP-MINUS-X))
 (225 207 (:REWRITE |(equal (- x) (- y))|))
 (214 214 (:REWRITE REDUCE-RATIONALP-+))
 (214 214 (:META META-RATIONALP-CORRECT))
 (210 210 (:REWRITE |(mod x (- y))| . 3))
 (210 210 (:REWRITE |(mod x (- y))| . 2))
 (210 210 (:REWRITE |(mod x (- y))| . 1))
 (210 210 (:REWRITE |(mod (- x) y)| . 3))
 (210 210 (:REWRITE |(mod (- x) y)| . 2))
 (210 210 (:REWRITE |(mod (- x) y)| . 1))
 (207 207
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (207 207
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (207 207
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (207 207 (:REWRITE |(equal c (/ x))|))
 (207 207 (:REWRITE |(equal c (- x))|))
 (207 207 (:REWRITE |(equal (/ x) c)|))
 (207 207 (:REWRITE |(equal (/ x) (/ y))|))
 (207 207 (:REWRITE |(equal (- x) c)|))
 (198 198 (:REWRITE |(- (* c x))|))
 (198 27
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (181 181
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (81 81
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (77 77 (:LINEAR RTL::MOD-BND-3))
 (72 3 (:REWRITE MOD-POSITIVE . 3))
 (60 6 (:REWRITE MOD-NEGATIVE . 2))
 (57 3 (:REWRITE MOD-NONPOSITIVE))
 (51 3 (:REWRITE MOD-ZERO . 1))
 (46 13 (:REWRITE INTEGERP-MOD-3))
 (46 13 (:REWRITE INTEGERP-MOD-2))
 (46 13 (:REWRITE INTEGERP-MOD-1))
 (46 13 (:REWRITE RTL::INTEGERP-MOD))
 (36 4 (:REWRITE RTL::RATIONALP-MOD))
 (30 3 (:REWRITE MOD-POSITIVE . 2))
 (27 3 (:REWRITE MOD-ZERO . 2))
 (24 24 (:REWRITE |(equal (+ (- c) x) y)|))
 (24 4 (:REWRITE RATIONALP-MOD))
 (6 6 (:REWRITE MOD-NEGATIVE . 1))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE MOD-POSITIVE . 1)))
(RTL::MOD-PROD
     (1165 7 (:REWRITE RTL::MOD-DOES-NOTHING))
     (1050 57
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (345 61 (:REWRITE DEFAULT-TIMES-2))
     (300 300
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (300 300
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (300 300
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (300 300
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (292 60 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (260 60
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (260 60
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (234 14 (:REWRITE |(* y (* x z))|))
     (220 2 (:LINEAR MOD-BOUNDS-3))
     (150 2 (:REWRITE |(* (* x y) z)|))
     (140 4 (:LINEAR MOD-BOUNDS-2))
     (140 4 (:LINEAR MOD-BOUNDS-1))
     (126 14 (:REWRITE |(* a (/ a) b)|))
     (120 60 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (120 27 (:REWRITE |(< 0 (/ x))|))
     (108 3 (:REWRITE |(< (if a b c) x)|))
     (106 4 (:REWRITE MOD-X-Y-=-X . 4))
     (106 4 (:REWRITE MOD-X-Y-=-X . 3))
     (103 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (103 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (103 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (103 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (90 3
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (90 3
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (81 6 (:REWRITE |(< x (if a b c))|))
     (71 29 (:REWRITE |(equal (/ x) c)|))
     (69 69 (:REWRITE THE-FLOOR-BELOW))
     (69 69 (:REWRITE THE-FLOOR-ABOVE))
     (69 69 (:REWRITE DEFAULT-LESS-THAN-2))
     (69 69 (:REWRITE DEFAULT-LESS-THAN-1))
     (64 4 (:REWRITE MOD-ZERO . 3))
     (64 2 (:LINEAR RTL::MOD-BND-2))
     (61 61 (:REWRITE DEFAULT-TIMES-1))
     (60 60 (:TYPE-PRESCRIPTION NATP))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (60 60
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (60 60 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (60 60 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (60 60
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (60 60
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (60 60
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (60 60
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (60 60
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (60 60
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (60 60
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (60 60
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (60 60
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (60 60
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (60 60
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (60 60
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (60 60
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (60 60 (:REWRITE |(< (/ x) (/ y))|))
     (60 60 (:REWRITE |(< (- x) (- y))|))
     (57 57
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (57 57 (:REWRITE INTEGERP-<-CONSTANT))
     (57 57 (:REWRITE CONSTANT-<-INTEGERP))
     (57 57 (:REWRITE |(< c (- x))|))
     (57 57 (:REWRITE |(< (- x) c)|))
     (55 4 (:REWRITE MOD-ZERO . 4))
     (55 4 (:REWRITE MOD-X-Y-=-X . 2))
     (55 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (55 4
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (54 54 (:REWRITE SIMPLIFY-SUMS-<))
     (54 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (43 4 (:REWRITE CANCEL-MOD-+))
     (40 4 (:REWRITE DEFAULT-MOD-RATIO))
     (34 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (31 31
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (29 29
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (29 29 (:REWRITE |(equal c (/ x))|))
     (29 29 (:REWRITE |(equal (/ x) (/ y))|))
     (29 29 (:REWRITE |(equal (- x) (- y))|))
     (27 27 (:REWRITE |(< 0 (* x y))|))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (26 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (26 26
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26 26
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (26 26
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (26 26 (:REWRITE |(equal c (- x))|))
     (26 26 (:REWRITE |(equal (- x) c)|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (21 21 (:REWRITE |(< (/ x) 0)|))
     (21 21 (:REWRITE |(< (* x y) 0)|))
     (20 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (20 4
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (20 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (19 19 (:REWRITE DEFAULT-DIVIDE))
     (16 4 (:REWRITE MOD-CANCEL-*-CONST))
     (16 2 (:REWRITE |(/ (* x y))|))
     (12 3 (:REWRITE RATIONALP-X))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (10 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (10 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (10 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (10 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (6 6
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (6 6 (:REWRITE |(/ (/ x))|))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
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
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE |(not (equal x (/ y)))|))
     (3 3 (:REWRITE |(equal x (/ y))|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:DEFINITION FIX))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (2 2 (:REWRITE |(* c (* d x))|))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::MOD-MOD-TIMES
     (2003 22 (:REWRITE RTL::MOD-DOES-NOTHING))
     (1288 1288
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1288 1288
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1288 1288
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1201 15 (:REWRITE CANCEL-MOD-+))
     (1080 216 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1080 216 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1016 216
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1016 216
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (774 45 (:REWRITE |(* (* x y) z)|))
     (670 4 (:LINEAR MOD-BOUNDS-3))
     (594 15 (:REWRITE MOD-ZERO . 3))
     (590 15 (:REWRITE |(integerp (- x))|))
     (504 15 (:REWRITE MOD-X-Y-=-X . 4))
     (504 15 (:REWRITE MOD-X-Y-=-X . 3))
     (492 4 (:LINEAR RTL::MOD-BND-2))
     (490 15 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (487 169 (:REWRITE DEFAULT-TIMES-2))
     (435 15 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (360 15 (:REWRITE DEFAULT-MOD-RATIO))
     (360 15 (:REWRITE |(* (- x) y)|))
     (351 169 (:REWRITE DEFAULT-TIMES-1))
     (338 53 (:META META-INTEGERP-CORRECT))
     (316 82
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (316 82 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (316 82 (:REWRITE DEFAULT-LESS-THAN-1))
     (266 15 (:REWRITE MOD-ZERO . 4))
     (264 82 (:REWRITE SIMPLIFY-SUMS-<))
     (216 216 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (216 216 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (216 216
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (216 216
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (216 216
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (199 31 (:REWRITE INTEGERP-/))
     (186 2 (:REWRITE |(* y (* x z))|))
     (144 8 (:LINEAR MOD-BOUNDS-2))
     (131 15 (:REWRITE DEFAULT-MINUS))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (108 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (104 104
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (82 82 (:REWRITE THE-FLOOR-BELOW))
     (82 82 (:REWRITE THE-FLOOR-ABOVE))
     (82 82
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (82 82
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (82 82
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (82 82
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (82 82 (:REWRITE INTEGERP-<-CONSTANT))
     (82 82 (:REWRITE DEFAULT-LESS-THAN-2))
     (82 82 (:REWRITE CONSTANT-<-INTEGERP))
     (82 82
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (82 82
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (82 82
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (82 82
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (82 82 (:REWRITE |(< c (- x))|))
     (82 82
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (82 82
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (82 82
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (82 82
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (82 82 (:REWRITE |(< (/ x) (/ y))|))
     (82 82 (:REWRITE |(< (- x) c)|))
     (82 82 (:REWRITE |(< (- x) (- y))|))
     (75 15 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (75 15 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (75 15 (:REWRITE MOD-X-Y-=-X . 2))
     (75 15
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (75 15
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (75 15 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (75 15
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (75 15
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (71 15 (:REWRITE MOD-CANCEL-*-CONST))
     (58 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (53 53 (:REWRITE REDUCE-INTEGERP-+))
     (53 53 (:REWRITE INTEGERP-MINUS-X))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (48 48 (:REWRITE DEFAULT-DIVIDE))
     (47 47 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (45 45 (:REWRITE |(* c (* d x))|))
     (44 22 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (32 32 (:REWRITE |(< (/ x) 0)|))
     (32 32 (:REWRITE |(< (* x y) 0)|))
     (30 30
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (28 28 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (28 28
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (28 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (28 28
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (28 28
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (28 28
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (28 28 (:REWRITE |(equal c (/ x))|))
     (28 28 (:REWRITE |(equal c (- x))|))
     (28 28 (:REWRITE |(equal (/ x) c)|))
     (28 28 (:REWRITE |(equal (/ x) (/ y))|))
     (28 28 (:REWRITE |(equal (- x) c)|))
     (28 28 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:TYPE-PRESCRIPTION NATP))
     (22 22 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (16 16 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (16 16 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (15 15 (:REWRITE DEFAULT-MOD-2))
     (15 15 (:REWRITE DEFAULT-MOD-1))
     (15 15 (:REWRITE |(mod x (- y))| . 3))
     (15 15 (:REWRITE |(mod x (- y))| . 2))
     (15 15 (:REWRITE |(mod x (- y))| . 1))
     (15 15
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (15 15 (:REWRITE |(mod (- x) y)| . 3))
     (15 15 (:REWRITE |(mod (- x) y)| . 2))
     (15 15 (:REWRITE |(mod (- x) y)| . 1))
     (15 15
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (15 15 (:REWRITE |(- (* c x))|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (13 13 (:REWRITE |(equal (* x y) 0)|))
     (13 13
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (4 4 (:LINEAR RTL::MOD-BND-3)))
(RTL::MOD-PLUS-MOD
     (4446 4446
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4446 4446
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4446 4446
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (3689 85 (:REWRITE CANCEL-MOD-+))
     (2963 85 (:REWRITE MOD-X-Y-=-X . 4))
     (2963 85 (:REWRITE MOD-X-Y-=-X . 3))
     (2879 85 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (2815 563 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2775 563 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2727 563
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2727 563
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2627 85 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2207 85 (:REWRITE RTL::MOD-DOES-NOTHING))
     (2172 85 (:REWRITE MOD-ZERO . 3))
     (1673 113 (:REWRITE DEFAULT-PLUS-2))
     (1648 113 (:REWRITE DEFAULT-PLUS-1))
     (1536 96 (:REWRITE |(integerp (- x))|))
     (1524 85 (:REWRITE MOD-ZERO . 4))
     (1202 85 (:REWRITE DEFAULT-MOD-RATIO))
     (1008 436 (:REWRITE SIMPLIFY-SUMS-<))
     (1008 436
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1008 436
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1008 436 (:REWRITE DEFAULT-LESS-THAN-1))
     (960 96 (:REWRITE |(* (- x) y)|))
     (725 75 (:REWRITE |(* y x)|))
     (625 25 (:REWRITE |(* x (+ y z))|))
     (563 563 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (563 563 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (563 563
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (563 563
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (563 563
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (497 109 (:REWRITE DEFAULT-MINUS))
     (493 493 (:REWRITE DEFAULT-TIMES-2))
     (493 493 (:REWRITE DEFAULT-TIMES-1))
     (478 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (461 88
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (436 436 (:REWRITE THE-FLOOR-BELOW))
     (436 436 (:REWRITE THE-FLOOR-ABOVE))
     (436 436
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (436 436
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (436 436
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (436 436
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (436 436 (:REWRITE INTEGERP-<-CONSTANT))
     (436 436 (:REWRITE DEFAULT-LESS-THAN-2))
     (436 436 (:REWRITE CONSTANT-<-INTEGERP))
     (436 436
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (436 436
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (436 436
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (436 436
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (436 436 (:REWRITE |(< c (- x))|))
     (436 436
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (436 436
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (436 436
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (436 436
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (436 436 (:REWRITE |(< (/ x) (/ y))|))
     (436 436 (:REWRITE |(< (- x) c)|))
     (436 436 (:REWRITE |(< (- x) (- y))|))
     (425 85 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (425 85 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (425 85 (:REWRITE MOD-X-Y-=-X . 2))
     (425 85
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (425 85
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (425 85 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (425 85
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (425 85
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (322 322
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (272 272
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (272 272 (:REWRITE DEFAULT-DIVIDE))
     (268 268 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (260 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (245 85 (:REWRITE MOD-CANCEL-*-CONST))
     (218 88
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (216 5 (:LINEAR MOD-BOUNDS-3))
     (193 189 (:REWRITE INTEGERP-MINUS-X))
     (191 87 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (189 189 (:REWRITE REDUCE-INTEGERP-+))
     (189 189 (:META META-INTEGERP-CORRECT))
     (173 173
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (173 173
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (173 173 (:REWRITE |(< (/ x) 0)|))
     (173 173 (:REWRITE |(< (* x y) 0)|))
     (161 5 (:LINEAR RTL::MOD-BND-2))
     (97 97 (:REWRITE |(- (* c x))|))
     (93 87 (:REWRITE NORMALIZE-ADDENDS))
     (88 88
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (88 88
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (88 88
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (88 88 (:REWRITE |(equal c (/ x))|))
     (88 88 (:REWRITE |(equal c (- x))|))
     (88 88 (:REWRITE |(equal (/ x) c)|))
     (88 88 (:REWRITE |(equal (/ x) (/ y))|))
     (88 88 (:REWRITE |(equal (- x) c)|))
     (88 88 (:REWRITE |(equal (- x) (- y))|))
     (86 86
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (85 85
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (85 85 (:REWRITE DEFAULT-MOD-2))
     (85 85 (:REWRITE DEFAULT-MOD-1))
     (85 85 (:REWRITE |(mod x (- y))| . 3))
     (85 85 (:REWRITE |(mod x (- y))| . 2))
     (85 85 (:REWRITE |(mod x (- y))| . 1))
     (85 85
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (85 85 (:REWRITE |(mod (- x) y)| . 3))
     (85 85 (:REWRITE |(mod (- x) y)| . 2))
     (85 85 (:REWRITE |(mod (- x) y)| . 1))
     (85 85
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (84 84
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (84 84
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (84 84
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (84 84 (:REWRITE |(< 0 (/ x))|))
     (84 84 (:REWRITE |(< 0 (* x y))|))
     (61 1
         (:REWRITE |(equal (mod a n) (mod b n))|))
     (58 58 (:REWRITE |(< (+ c/d x) y)|))
     (58 58 (:REWRITE |(< (+ (- c) x) y)|))
     (50 10 (:LINEAR MOD-BOUNDS-2))
     (44 22 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (22 22 (:TYPE-PRESCRIPTION NATP))
     (22 22 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (22 22
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (15 15
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 12 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (11 11 (:REWRITE FOLD-CONSTS-IN-+))
     (11 11
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (11 11
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|))
     (11 11 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:LINEAR RTL::MOD-BND-3))
     (3 3
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (2 2 (:DEFINITION FIX))
     (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE |(+ x (- x))|))
     (1 1 (:REWRITE |(+ 0 x)|)))
(RTL::MOD-TIMES-MOD
     (12924 16 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (8242 8242
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (8242 8242
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8242 8242
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7329 203
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6536 16 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (6109 1229 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (5177 1229
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (5177 1229
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (4804 128 (:REWRITE MOD-X-Y-=-X . 4))
     (4804 128 (:REWRITE MOD-X-Y-=-X . 3))
     (4794 132 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (4274 132 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (3949 1721 (:REWRITE DEFAULT-TIMES-2))
     (3870 133 (:REWRITE RTL::MOD-DOES-NOTHING))
     (3537 121 (:REWRITE |(integerp (- x))|))
     (3351 132 (:REWRITE DEFAULT-MOD-RATIO))
     (2773 132 (:REWRITE MOD-ZERO . 4))
     (2111 1721 (:REWRITE DEFAULT-TIMES-1))
     (1785 295 (:REWRITE DEFAULT-PLUS-2))
     (1533 453 (:REWRITE INTEGERP-MINUS-X))
     (1462 440 (:META META-INTEGERP-CORRECT))
     (1229 1229 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1229 1229 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1229 1229
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1229 1229
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1227 1227
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1179 171 (:REWRITE DEFAULT-MINUS))
     (1070 32 (:LINEAR RTL::MOD-BND-2))
     (997 662
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (897 897
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (842 660
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (820 664 (:REWRITE DEFAULT-LESS-THAN-1))
     (815 295 (:REWRITE DEFAULT-PLUS-1))
     (749 203
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (748 184 (:REWRITE INTEGERP-/))
     (692 128 (:REWRITE MOD-X-Y-=-X . 2))
     (692 128
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (692 128
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (690 664 (:REWRITE DEFAULT-LESS-THAN-2))
     (682 132 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (682 132 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (680 680
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (680 680
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (680 680
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (680 680
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (667 667 (:REWRITE THE-FLOOR-BELOW))
     (667 667 (:REWRITE THE-FLOOR-ABOVE))
     (664 664
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (664 664
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (664 664
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (662 662
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (662 662 (:REWRITE INTEGERP-<-CONSTANT))
     (662 662 (:REWRITE CONSTANT-<-INTEGERP))
     (662 662
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (662 662
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (662 662
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (662 662
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (662 662 (:REWRITE |(< c (- x))|))
     (662 662
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (662 662
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (662 662
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (662 662
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (662 662 (:REWRITE |(< (/ x) (/ y))|))
     (662 662 (:REWRITE |(< (- x) c)|))
     (662 662 (:REWRITE |(< (- x) (- y))|))
     (611 195 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (595 127 (:REWRITE MOD-CANCEL-*-CONST))
     (491 127
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (479 240 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (467 127
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (467 127
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (452 452 (:REWRITE DEFAULT-DIVIDE))
     (451 451
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (439 283
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (439 283
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (414 414 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (352 4
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (348 12 (:REWRITE |(- (+ x y))|))
     (310 62 (:LINEAR MOD-BOUNDS-2))
     (305 305
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (305 305
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (305 305
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (297 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (283 283 (:REWRITE |(< (/ x) 0)|))
     (283 283 (:REWRITE |(< (* x y) 0)|))
     (283 283 (:REWRITE |(* c (* d x))|))
     (271 127
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (271 127
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (271 127
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (240 240
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (240 240 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (240 240 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (240 240
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (239 239 (:TYPE-PRESCRIPTION NATP))
     (218 204 (:REWRITE |(equal (/ x) c)|))
     (210 132
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (204 204
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (204 204
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (204 204 (:REWRITE |(equal c (/ x))|))
     (204 204 (:REWRITE |(equal (/ x) (/ y))|))
     (204 204 (:REWRITE |(equal (- x) (- y))|))
     (203 203
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (203 203 (:REWRITE |(equal c (- x))|))
     (203 203 (:REWRITE |(equal (- x) c)|))
     (202 124
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (202 124
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (195 195 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (194 194
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (158 132 (:REWRITE DEFAULT-MOD-1))
     (146 4 (:REWRITE MOD-ZERO . 1))
     (139 139 (:REWRITE |(- (* c x))|))
     (132 132 (:REWRITE DEFAULT-MOD-2))
     (127 127 (:REWRITE |(mod x (- y))| . 3))
     (127 127 (:REWRITE |(mod x (- y))| . 2))
     (127 127 (:REWRITE |(mod x (- y))| . 1))
     (127 127 (:REWRITE |(mod (- x) y)| . 3))
     (127 127 (:REWRITE |(mod (- x) y)| . 2))
     (127 127 (:REWRITE |(mod (- x) y)| . 1))
     (126 126 (:REWRITE |(< 0 (* x y))|))
     (124 124 (:REWRITE |(< 0 (/ x))|))
     (122 122
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (85 85 (:REWRITE |(equal (* x y) 0)|))
     (83 83
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (60 12 (:REWRITE |(- (- x))|))
     (54 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (32 32 (:LINEAR RTL::MOD-BND-3))
     (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (26 26 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (26 26
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (21 21 (:REWRITE |(equal (+ (- c) x) y)|))
     (20 4 (:REWRITE MOD-ZERO . 2))
     (16 16
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (16 16 (:REWRITE |(+ c (+ d x))|))
     (9 9 (:REWRITE |(< (+ c/d x) y)|))
     (9 9 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE MOD-NEGATIVE . 3))
     (2 2 (:REWRITE MOD-NEGATIVE . 2))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE MOD-POSITIVE . 3))
     (1 1 (:REWRITE MOD-POSITIVE . 2))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(RTL::MOD012 (125 25 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
             (125 25 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
             (113 25
                  (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
             (113 25
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
             (106 106
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
             (106 106
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
             (106 106
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
             (106 106
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
             (52 2 (:REWRITE RTL::MOD-DOES-NOTHING))
             (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
             (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
             (25 25
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
             (25 25 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
             (25 25
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
             (18 2 (:REWRITE DEFAULT-MOD-RATIO))
             (8 2 (:REWRITE |(* y x)|))
             (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
             (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
             (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
             (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
             (6 6 (:REWRITE DEFAULT-TIMES-2))
             (6 6 (:REWRITE DEFAULT-TIMES-1))
             (6 3 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
             (4 4
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (3 3
                (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
             (3 3 (:TYPE-PRESCRIPTION RATIONALP-MOD))
             (3 3 (:TYPE-PRESCRIPTION NATP))
             (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
             (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
             (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
             (3 3
                (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
             (3 3 (:REWRITE REDUCE-INTEGERP-+))
             (3 3 (:REWRITE INTEGERP-MINUS-X))
             (3 3 (:META META-INTEGERP-CORRECT))
             (2 2 (:REWRITE THE-FLOOR-BELOW))
             (2 2 (:REWRITE THE-FLOOR-ABOVE))
             (2 2 (:REWRITE SIMPLIFY-SUMS-<))
             (2 2
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
             (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
             (2 2
                (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
             (2 2
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
             (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
             (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
             (2 2 (:REWRITE INTEGERP-<-CONSTANT))
             (2 2 (:REWRITE DEFAULT-MOD-2))
             (2 2 (:REWRITE DEFAULT-MOD-1))
             (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
             (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
             (2 2 (:REWRITE CONSTANT-<-INTEGERP))
             (2 2 (:REWRITE |(mod x 2)| . 2))
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
             (2 2 (:REWRITE |(< (- x) (- y))|)))
(RTL::MOD-PLUS-MOD-RADIX
     (63519 41 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (47924 41 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (15325 15325
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (10260 2100 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (10132 2100 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (9897 339 (:REWRITE MOD-X-Y-=-X . 3))
     (9864 2100
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (9864 2100
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7449 139 (:LINEAR RTL::MOD-BND-2))
     (6951 342 (:REWRITE MOD-ZERO . 3))
     (6471 780 (:REWRITE DEFAULT-PLUS-2))
     (5391 342 (:REWRITE MOD-ZERO . 4))
     (4429 342 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (4227 342 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (4200 2100 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (4006 342 (:REWRITE DEFAULT-MOD-RATIO))
     (3737 342 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (3481 342 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (3476 780 (:REWRITE DEFAULT-PLUS-1))
     (3315 138 (:LINEAR MOD-BOUNDS-3))
     (3033 492
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2100 2100 (:TYPE-PRESCRIPTION NATP))
     (2100 2100 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (2100 2100 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2100 2100
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2100 2100
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2100 2100
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2100 2100
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2100 2100
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (2008 1671
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2008 1671
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1935 1671 (:REWRITE DEFAULT-LESS-THAN-1))
     (1744 1671 (:REWRITE DEFAULT-LESS-THAN-2))
     (1720 1716 (:REWRITE DEFAULT-TIMES-2))
     (1716 1716 (:REWRITE DEFAULT-TIMES-1))
     (1671 1671 (:REWRITE THE-FLOOR-BELOW))
     (1671 1671 (:REWRITE THE-FLOOR-ABOVE))
     (1671 1671
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1671 1671
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1671 1671
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1671 1671
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1671 1671 (:REWRITE INTEGERP-<-CONSTANT))
     (1671 1671 (:REWRITE CONSTANT-<-INTEGERP))
     (1671 1671
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1671 1671
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1671 1671
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1671 1671
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1671 1671 (:REWRITE |(< c (- x))|))
     (1671 1671
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1671 1671
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1671 1671
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1671 1671
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1671 1671 (:REWRITE |(< (/ x) (/ y))|))
     (1671 1671 (:REWRITE |(< (- x) c)|))
     (1671 1671 (:REWRITE |(< (- x) (- y))|))
     (1433 337 (:REWRITE MOD-CANCEL-*-CONST))
     (1318 339 (:REWRITE MOD-X-Y-=-X . 2))
     (1318 339
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (1318 339
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (1297 337
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1297 337
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1297 337
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1156 1156
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (982 982
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (982 982 (:REWRITE DEFAULT-DIVIDE))
     (874 206 (:REWRITE DEFAULT-MINUS))
     (858 858 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (725 337
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (725 337
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (725 337
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (723 723
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (723 723
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (723 723 (:REWRITE |(< (/ x) 0)|))
     (723 723 (:REWRITE |(< (* x y) 0)|))
     (652 632 (:META META-INTEGERP-CORRECT))
     (632 632 (:REWRITE REDUCE-INTEGERP-+))
     (632 632 (:REWRITE INTEGERP-MINUS-X))
     (492 492
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (492 492
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (492 492
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (492 492 (:REWRITE |(equal c (/ x))|))
     (492 492 (:REWRITE |(equal c (- x))|))
     (492 492 (:REWRITE |(equal (/ x) c)|))
     (492 492 (:REWRITE |(equal (/ x) (/ y))|))
     (492 492 (:REWRITE |(equal (- x) c)|))
     (492 492 (:REWRITE |(equal (- x) (- y))|))
     (453 3
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (432 90 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (420 420
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (420 420
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (420 420 (:REWRITE |(< 0 (/ x))|))
     (420 420 (:REWRITE |(< 0 (* x y))|))
     (397 397
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (342 342 (:REWRITE DEFAULT-MOD-2))
     (342 342 (:REWRITE DEFAULT-MOD-1))
     (337 337 (:REWRITE |(mod x (- y))| . 3))
     (337 337 (:REWRITE |(mod x (- y))| . 2))
     (337 337 (:REWRITE |(mod x (- y))| . 1))
     (337 337 (:REWRITE |(mod (- x) y)| . 3))
     (337 337 (:REWRITE |(mod (- x) y)| . 2))
     (337 337 (:REWRITE |(mod (- x) y)| . 1))
     (241 241
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (171 171 (:REWRITE |(- (* c x))|))
     (150 6 (:REWRITE MOD-ZERO . 1))
     (139 139 (:LINEAR RTL::MOD-BND-3))
     (101 101 (:REWRITE |(equal (+ (- c) x) y)|))
     (84 21 (:REWRITE RATIONALP-X))
     (82 6 (:REWRITE MOD-ZERO . 2))
     (67 67 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (55 55 (:REWRITE |(< (+ c/d x) y)|))
     (55 55 (:REWRITE |(< (+ (- c) x) y)|))
     (55 55 (:REWRITE |(+ c (+ d x))|))
     (41 41
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (40 10 (:REWRITE |(+ x x)|))
     (27 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (24 24 (:REWRITE |(< y (+ (- c) x))|))
     (24 24 (:REWRITE |(< x (+ c/d y))|))
     (23 23
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (21 21 (:REWRITE REDUCE-RATIONALP-+))
     (21 21 (:REWRITE REDUCE-RATIONALP-*))
     (21 21 (:REWRITE RATIONALP-MINUS-X))
     (21 21 (:REWRITE FOLD-CONSTS-IN-+))
     (21 21 (:META META-RATIONALP-CORRECT))
     (15 15
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (15 15
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (7 7
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (7 7
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (6 6 (:REWRITE MOD-X-Y-=-X . 1))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|)))
(RTL::MOD-PLUS-MOD-2)
(RTL::MOD-MOD-2-NOT-EQUAL
     (37995 10 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (33599 170
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (30480 98 (:LINEAR MOD-BOUNDS-1))
     (30246 10 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (8745 165 (:REWRITE CANCEL-MOD-+))
     (5371 49 (:LINEAR RTL::MOD-BND-2))
     (5354 5354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5354 5354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5354 5354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4995 165 (:REWRITE MOD-X-Y-=-X . 4))
     (4854 165 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (4755 165 (:REWRITE MOD-X-Y-=-X . 3))
     (4572 168 (:REWRITE RTL::MOD-DOES-NOTHING))
     (4497 702 (:REWRITE INTEGERP-MINUS-X))
     (4413 165 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (3630 726 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3630 726 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3394 726
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (3394 726
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (3204 165 (:REWRITE MOD-ZERO . 3))
     (2805 330 (:REWRITE |(* (- x) y)|))
     (2590 165 (:REWRITE MOD-ZERO . 4))
     (2501 207 (:REWRITE DEFAULT-PLUS-2))
     (1685 1685
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1685 1685
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1685 1685
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1685 1685
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1653 1585 (:REWRITE DEFAULT-TIMES-2))
     (1650 330 (:REWRITE DEFAULT-MINUS))
     (1585 1585 (:REWRITE DEFAULT-TIMES-1))
     (1485 330 (:REWRITE |(- (* c x))|))
     (1452 726 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (1272 784
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1117 49 (:LINEAR MOD-BOUNDS-3))
     (873 873
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (850 784 (:REWRITE DEFAULT-LESS-THAN-1))
     (837 771
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (825 165 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (825 165 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (825 165 (:REWRITE MOD-X-Y-=-X . 2))
     (825 165
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (825 165
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (789 165
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (789 165
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (784 784 (:REWRITE THE-FLOOR-BELOW))
     (784 784 (:REWRITE THE-FLOOR-ABOVE))
     (784 784
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (784 784
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (784 784 (:REWRITE DEFAULT-LESS-THAN-2))
     (771 771 (:REWRITE SIMPLIFY-SUMS-<))
     (771 771
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (771 771
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (771 771 (:REWRITE INTEGERP-<-CONSTANT))
     (771 771 (:REWRITE CONSTANT-<-INTEGERP))
     (771 771
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (771 771
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (771 771
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (771 771
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (771 771 (:REWRITE |(< c (- x))|))
     (771 771
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (771 771
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (771 771
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (771 771
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (771 771 (:REWRITE |(< (/ x) (/ y))|))
     (771 771 (:REWRITE |(< (- x) c)|))
     (771 771 (:REWRITE |(< (- x) (- y))|))
     (741 207 (:REWRITE DEFAULT-PLUS-1))
     (726 726 (:TYPE-PRESCRIPTION NATP))
     (726 726 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (726 726 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (726 726
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (726 726
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (726 726
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (726 726 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (726 726 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (726 726
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (713 165 (:REWRITE MOD-CANCEL-*-CONST))
     (684 156
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (684 156
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (636 98 (:LINEAR MOD-BOUNDS-2))
     (561 165 (:REWRITE |(mod x 2)| . 2))
     (537 537 (:REWRITE REDUCE-INTEGERP-+))
     (537 537 (:META META-INTEGERP-CORRECT))
     (450 21 (:REWRITE RATIONALP-X))
     (414 414 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (374 11 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (295 295 (:REWRITE |(< (* x y) 0)|))
     (290 290
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (290 290
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (290 290 (:REWRITE |(< (/ x) 0)|))
     (201 165
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (201 165
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (200 165 (:REWRITE |(mod x 2)| . 1))
     (170 170
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE DEFAULT-MOD-2))
     (168 168 (:REWRITE DEFAULT-MOD-1))
     (165 165 (:REWRITE |(mod x (- y))| . 3))
     (165 165 (:REWRITE |(mod x (- y))| . 2))
     (165 165 (:REWRITE |(mod x (- y))| . 1))
     (165 165
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (165 165
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (165 165 (:REWRITE |(mod (- x) y)| . 3))
     (165 165 (:REWRITE |(mod (- x) y)| . 2))
     (165 165 (:REWRITE |(mod (- x) y)| . 1))
     (156 156
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (156 156 (:REWRITE |(equal c (/ x))|))
     (156 156 (:REWRITE |(equal c (- x))|))
     (156 156 (:REWRITE |(equal (/ x) c)|))
     (156 156 (:REWRITE |(equal (/ x) (/ y))|))
     (156 156 (:REWRITE |(equal (- x) c)|))
     (156 156 (:REWRITE |(equal (- x) (- y))|))
     (141 141 (:REWRITE |(< 0 (* x y))|))
     (139 139
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (139 139
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (139 139
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (139 139 (:REWRITE |(< 0 (/ x))|))
     (138 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (70 70
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (59 59 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (49 49 (:LINEAR RTL::MOD-BND-3))
     (21 21 (:REWRITE RATIONALP-MINUS-X))
     (15 15 (:REWRITE |(equal (+ (- c) x) y)|))
     (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (13 13 (:REWRITE |(< (+ c/d x) y)|))
     (11 11 (:META META-RATIONALP-CORRECT))
     (10 10
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (9 1 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::MOD-2*M+1-REWRITE
     (1881 64
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1694 75
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1264 8 (:REWRITE RTL::MOD-DOES-NOTHING))
     (708 3 (:LINEAR RTL::MOD-BND-2))
     (669 47 (:REWRITE INTEGERP-<-CONSTANT))
     (275 11
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (267 21 (:REWRITE |(* y x)|))
     (263 147 (:REWRITE DEFAULT-TIMES-2))
     (242 53 (:REWRITE |(< c (- x))|))
     (200 8 (:REWRITE DEFAULT-MOD-RATIO))
     (191 11
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (174 3
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (170 34 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (170 34 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (162 34
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (162 34
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (147 147 (:REWRITE DEFAULT-TIMES-1))
     (121 11 (:REWRITE |(+ y (+ x z))|))
     (84 64
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (75 75 (:REWRITE THE-FLOOR-BELOW))
     (75 75 (:REWRITE THE-FLOOR-ABOVE))
     (75 75 (:REWRITE DEFAULT-LESS-THAN-2))
     (75 75 (:REWRITE DEFAULT-LESS-THAN-1))
     (68 68
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (63 63 (:REWRITE DEFAULT-PLUS-2))
     (63 63 (:REWRITE DEFAULT-PLUS-1))
     (58 2 (:LINEAR MOD-BOUNDS-3))
     (53 53
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (53 53
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (53 53
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (53 53
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (53 53
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (53 53
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (53 53
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (53 53
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (53 53 (:REWRITE |(< (/ x) (/ y))|))
     (53 53 (:REWRITE |(< (- x) (- y))|))
     (51 51 (:TYPE-PRESCRIPTION ABS))
     (47 47 (:REWRITE CONSTANT-<-INTEGERP))
     (47 47 (:REWRITE |(< (- x) c)|))
     (44 11 (:REWRITE |(+ c (+ d x))|))
     (36 36 (:REWRITE SIMPLIFY-SUMS-<))
     (36 36
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (36 36
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (36 36 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (34 34 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (34 34 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (34 34
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (34 34 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (34 34
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (30 30 (:REWRITE NORMALIZE-ADDENDS))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (24 6 (:REWRITE |(- (* c x))|))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< 0 (/ x))|))
     (16 16 (:REWRITE |(< 0 (* x y))|))
     (11 11 (:REWRITE |(< (+ c/d x) y)|))
     (11 11 (:REWRITE |(+ 0 x)|))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (8 8 (:REWRITE DEFAULT-MOD-1))
     (8 8 (:REWRITE |(mod x 2)| . 2))
     (6 6 (:REWRITE DEFAULT-MINUS))
     (6 6 (:REWRITE |(* (- x) y)|))
     (4 2 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(* x (- y))|))
     (3 3 (:LINEAR RTL::MOD-BND-3))
     (2 2
        (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (2 2 (:TYPE-PRESCRIPTION NATP))
     (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2 2
        (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD)))
(RTL::LEMMA
     (33392 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (26647 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (13339 13339
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (13339 13339
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (13339 13339
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (10148 225 (:REWRITE DEFAULT-PLUS-2))
     (9964 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7514 45
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6473 114 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (6243 225 (:REWRITE DEFAULT-PLUS-1))
     (6064 1620
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6064 1620
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6064 1620
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (6064 1620
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (6064 1620
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3896 1620
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3060 686 (:REWRITE DEFAULT-TIMES-1))
     (2285 457 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2285 457 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2233 686 (:REWRITE DEFAULT-TIMES-2))
     (2072 21 (:REWRITE CANCEL-MOD-+))
     (1903 21 (:REWRITE MOD-X-Y-=-X . 3))
     (1850 21 (:REWRITE MOD-X-Y-=-X . 4))
     (1848 122 (:REWRITE THE-FLOOR-ABOVE))
     (1757 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1752 21 (:REWRITE MOD-ZERO . 4))
     (1687 28 (:REWRITE FLOOR-ZERO . 3))
     (1661 9 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (1604 21 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (1576 157 (:REWRITE RATIONALP-X))
     (1549 457
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1549 457
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1444 289
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1346 3 (:REWRITE |(< (if a b c) x)|))
     (1252 28 (:REWRITE FLOOR-ZERO . 4))
     (1242 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1240 28 (:REWRITE FLOOR-ZERO . 5))
     (1240 28 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1016 49 (:REWRITE |(* (- x) y)|))
     (984 48 (:REWRITE |(integerp (- x))|))
     (978 57 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (954 45 (:REWRITE |(equal (- x) (- y))|))
     (920 28 (:REWRITE CANCEL-FLOOR-+))
     (871 21 (:REWRITE MOD-ZERO . 3))
     (826 113
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (788 92 (:REWRITE ACL2-NUMBERP-X))
     (782 6 (:LINEAR RTL::MOD-BND-2))
     (732 116 (:REWRITE DEFAULT-LESS-THAN-1))
     (728 113
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (728 57 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (664 335 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (617 11
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (526 28 (:REWRITE FLOOR-=-X/Y . 2))
     (518 56 (:REWRITE DEFAULT-MINUS))
     (487 28 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (481 457 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (457 457 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (457 457
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (457 457
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (457 457
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (448 28 (:REWRITE FLOOR-=-X/Y . 3))
     (343 21 (:REWRITE MOD-X-Y-=-X . 2))
     (343 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (343 21
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (333 333 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (333 333 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (329 329 (:TYPE-PRESCRIPTION NATP))
     (317 113 (:REWRITE SIMPLIFY-SUMS-<))
     (314 1 (:REWRITE |(* y (* x z))|))
     (297 297 (:REWRITE REDUCE-INTEGERP-+))
     (297 297 (:REWRITE INTEGERP-MINUS-X))
     (297 297 (:META META-INTEGERP-CORRECT))
     (289 289
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (289 289
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (289 289
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (268 116 (:REWRITE DEFAULT-LESS-THAN-2))
     (258 122 (:REWRITE THE-FLOOR-BELOW))
     (238 6 (:LINEAR MOD-BOUNDS-3))
     (224 21 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (224 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (224 21 (:REWRITE MOD-CANCEL-*-CONST))
     (182 182 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (176 21
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (160 22 (:REWRITE |(floor x 1)|))
     (157 157 (:REWRITE RATIONALP-MINUS-X))
     (155 155 (:REWRITE REDUCE-RATIONALP-+))
     (155 155 (:META META-RATIONALP-CORRECT))
     (154 20
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (154 20
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (128 12 (:LINEAR MOD-BOUNDS-2))
     (113 113
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (113 113
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (113 113
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (113 113
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (100 100
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (97 97
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (97 97 (:REWRITE DEFAULT-DIVIDE))
     (85 28 (:REWRITE FLOOR-ZERO . 2))
     (85 28 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (85 28 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (81 28 (:REWRITE FLOOR-CANCEL-*-CONST))
     (76 76 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (69 28
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (69 21
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (68 20
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (68 20
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (60 14 (:REWRITE FLOOR-NEGATIVE . 4))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (55 55 (:REWRITE |(< (/ x) 0)|))
     (55 55 (:REWRITE |(< (* x y) 0)|))
     (54 54
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (54 8 (:REWRITE FLOOR-NONNEGATIVE . 3))
     (54 6 (:REWRITE RTL::RATIONALP-MOD))
     (45 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (45 45
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (45 45 (:REWRITE |(equal c (/ x))|))
     (45 45 (:REWRITE |(equal c (- x))|))
     (45 45 (:REWRITE |(equal (/ x) c)|))
     (45 45 (:REWRITE |(equal (/ x) (/ y))|))
     (45 45 (:REWRITE |(equal (- x) c)|))
     (44 28
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (43 27
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (43 27
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (42 12 (:REWRITE INTEGERP-MOD-2))
     (42 12 (:REWRITE INTEGERP-MOD-1))
     (42 12 (:REWRITE RTL::INTEGERP-MOD))
     (36 6 (:REWRITE RATIONALP-MOD))
     (35 35 (:REWRITE DEFAULT-FLOOR-2))
     (35 27
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (35 27
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (32 32 (:REWRITE |(equal (+ (- c) x) y)|))
     (29 29 (:REWRITE |(- (* c x))|))
     (27 27 (:REWRITE |(floor x (- y))| . 2))
     (27 27 (:REWRITE |(floor x (- y))| . 1))
     (27 27 (:REWRITE |(floor (- x) y)| . 2))
     (27 27 (:REWRITE |(floor (- x) y)| . 1))
     (25 25 (:REWRITE DEFAULT-MOD-2))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (21 21 (:REWRITE |(< 0 (/ x))|))
     (21 21 (:REWRITE |(< 0 (* x y))|))
     (21 17
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (20 20 (:REWRITE |(mod x (- y))| . 3))
     (20 20 (:REWRITE |(mod x (- y))| . 2))
     (20 20 (:REWRITE |(mod x (- y))| . 1))
     (20 20 (:REWRITE |(mod (- x) y)| . 3))
     (20 20 (:REWRITE |(mod (- x) y)| . 2))
     (20 20 (:REWRITE |(mod (- x) y)| . 1))
     (19 19 (:REWRITE |(+ c (+ d x))|))
     (14 14 (:REWRITE FLOOR-NEGATIVE . 3))
     (14 14 (:REWRITE FLOOR-NEGATIVE . 2))
     (14 14 (:REWRITE FLOOR-NEGATIVE . 1))
     (13 1 (:REWRITE |(equal (* (/ x) y) 1)|))
     (10 10 (:REWRITE FOLD-CONSTS-IN-+))
     (9 1 (:REWRITE MOD-POSITIVE . 3))
     (8 8 (:REWRITE FLOOR-NONNEGATIVE . 2))
     (8 8 (:REWRITE FLOOR-NONNEGATIVE . 1))
     (7 7 (:REWRITE FLOOR-ZERO . 1))
     (7 7 (:REWRITE FLOOR-POSITIVE . 4))
     (7 7 (:REWRITE FLOOR-POSITIVE . 3))
     (7 7 (:REWRITE FLOOR-POSITIVE . 2))
     (7 7 (:REWRITE FLOOR-POSITIVE . 1))
     (7 7 (:REWRITE FLOOR-NONPOSITIVE . 3))
     (7 7 (:REWRITE FLOOR-NONPOSITIVE . 2))
     (7 7 (:REWRITE FLOOR-NONPOSITIVE . 1))
     (7 7 (:REWRITE |(mod (floor x y) z)| . 5))
     (7 7 (:REWRITE |(mod (floor x y) z)| . 4))
     (7 7 (:REWRITE |(mod (floor x y) z)| . 3))
     (7 7 (:REWRITE |(mod (floor x y) z)| . 2))
     (6 6 (:LINEAR RTL::MOD-BND-3))
     (5 5
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (5 5
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (5 1 (:REWRITE MOD-NONPOSITIVE))
     (3 3 (:REWRITE |(* 0 x)|))
     (1 1 (:REWRITE MOD-POSITIVE . 2))
     (1 1 (:REWRITE MOD-POSITIVE . 1))
     (1 1 (:REWRITE FLOOR-X-Y-=-1 . 1))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (1 1 (:REWRITE |(* a (/ a))|)))
(RTL::FL-MOD
     (3134 168 (:REWRITE RATIONALP-X))
     (1226 11 (:REWRITE RTL::INTEGERP-FL))
     (1034 136 (:META META-RATIONALP-CORRECT))
     (778 778
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (778 778
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (778 778
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (645 129 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (629 129 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (417 3 (:REWRITE MOD-X-Y-=-X . 4))
     (415 235 (:META META-INTEGERP-CORRECT))
     (399 3 (:REWRITE MOD-ZERO . 4))
     (390 228
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (381 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (381 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (381 3
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (362 8 (:REWRITE |(< (if a b c) x)|))
     (257 3 (:REWRITE CANCEL-MOD-+))
     (246 3 (:REWRITE MOD-ZERO . 3))
     (242 45 (:REWRITE DEFAULT-LESS-THAN-1))
     (235 235 (:REWRITE REDUCE-INTEGERP-+))
     (235 235 (:REWRITE INTEGERP-MINUS-X))
     (229 129
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (229 129
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (228 228
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (228 228
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (228 228
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (225 25 (:REWRITE RATIONALP-/))
     (208 104 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (196 4 (:REWRITE |(< x (if a b c))|))
     (169 3
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (169 3 (:REWRITE MOD-CANCEL-*-CONST))
     (169 3
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (169 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (161 21 (:REWRITE INTP-3))
     (150 5 (:REWRITE MOD-X-I*J))
     (143 143 (:REWRITE RATIONALP-MINUS-X))
     (136 136 (:REWRITE REDUCE-RATIONALP-+))
     (129 129 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (129 129 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (129 129
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (129 129
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (129 129
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (120 10 (:REWRITE INTP-1))
     (105 17 (:REWRITE ACL2-NUMBERP-X))
     (104 104 (:TYPE-PRESCRIPTION NATP))
     (104 104
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (104 104 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (104 104 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (104 104
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (103 103
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (100 100 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (87 1 (:REWRITE |(integerp (- x))|))
     (82 67 (:REWRITE INTEGERP-/))
     (80 80
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (72 72 (:TYPE-PRESCRIPTION INTP-*))
     (60 60 (:TYPE-PRESCRIPTION FIX))
     (60 4 (:REWRITE DEFAULT-PLUS-2))
     (51 31 (:REWRITE SIMPLIFY-SUMS-<))
     (51 31
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (51 31 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (45 45 (:REWRITE THE-FLOOR-BELOW))
     (45 45 (:REWRITE THE-FLOOR-ABOVE))
     (45 45 (:REWRITE DEFAULT-LESS-THAN-2))
     (44 44 (:REWRITE |(* c (* d x))|))
     (44 1 (:REWRITE |(* (- x) y)|))
     (43 3 (:REWRITE MOD-X-Y-=-X . 3))
     (42 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (37 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (31 31
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (31 31
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (31 31
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (31 31
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (31 31 (:REWRITE INTEGERP-<-CONSTANT))
     (31 31 (:REWRITE CONSTANT-<-INTEGERP))
     (31 31
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (31 31
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (31 31
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (31 31
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (31 31 (:REWRITE |(< c (- x))|))
     (31 31
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (31 31
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (31 31
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (31 31
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (31 31 (:REWRITE |(< (/ x) (/ y))|))
     (31 31 (:REWRITE |(< (- x) c)|))
     (31 31 (:REWRITE |(< (- x) (- y))|))
     (23 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (23 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (23 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (21 1 (:REWRITE DEFAULT-MINUS))
     (20 5 (:REWRITE MOD-X-I*J-V2))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14 (:REWRITE DEFAULT-MOD-2))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< 0 (/ x))|))
     (9 9 (:REWRITE |(< 0 (* x y))|))
     (8 8 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (7 3 (:REWRITE MOD-X-Y-=-X . 2))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE |(equal x (/ y))|))
     (4 4
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (4 4 (:LINEAR RTL::N<=FL-LINEAR))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3 (:REWRITE |(mod x (- y))| . 3))
     (3 3 (:REWRITE |(mod x (- y))| . 2))
     (3 3 (:REWRITE |(mod x (- y))| . 1))
     (3 3
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(mod (- x) y)| . 3))
     (3 3 (:REWRITE |(mod (- x) y)| . 2))
     (3 3 (:REWRITE |(mod (- x) y)| . 1))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(equal (* x y) 0)|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (1 1 (:REWRITE |(- (* c x))|)))
(RTL::RADIXP)
(RTL::RADIXP-FORWARD)
(RTL::CHOP-R
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
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (13 13
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::CHOP-R-MOD
 (10331 1102 (:REWRITE DEFAULT-LESS-THAN-2))
 (9727 46 (:REWRITE RTL::MOD-DOES-NOTHING))
 (7604 884 (:REWRITE ACL2-NUMBERP-X))
 (7178 904 (:REWRITE DEFAULT-LESS-THAN-1))
 (6435 781 (:REWRITE DEFAULT-TIMES-2))
 (5326 904 (:REWRITE RATIONALP-X))
 (5092 21
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (5026 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (4896 21 (:REWRITE CANCEL-MOD-+))
 (4372 12 (:LINEAR MOD-BOUNDS-2))
 (3911
  3731
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3731 3731
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (3731
      3731
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3731
     3731
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3731 3731
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3731 3731
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3731 3731
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (3675 3675
       (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3675 3675
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (3085 339 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2673 23 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2624 23 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2580 114 (:LINEAR EXPT-<=-1-ONE))
 (2489 114 (:LINEAR EXPT->=-1-TWO))
 (2489 114 (:LINEAR EXPT->-1-TWO))
 (2489 114 (:LINEAR EXPT-<-1-ONE))
 (2484 189 (:REWRITE DEFAULT-DIVIDE))
 (2475 321
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2475 321
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2475 321
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2348 114 (:LINEAR EXPT-X->=-X))
 (2348 114 (:LINEAR EXPT->=-1-ONE))
 (2348 114 (:LINEAR EXPT-<=-1-TWO))
 (2346 781 (:REWRITE DEFAULT-TIMES-1))
 (2313 23 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2313 23 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2257 339 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2257 114 (:LINEAR EXPT-X->-X))
 (2257 114 (:LINEAR EXPT->-1-ONE))
 (2257 114 (:LINEAR EXPT-<-1-TWO))
 (2026 328 (:REWRITE DEFAULT-PLUS-2))
 (1946 23 (:REWRITE MOD-ZERO . 3))
 (1926 10 (:REWRITE |(< x (if a b c))|))
 (1906 904 (:REWRITE REDUCE-RATIONALP-*))
 (1826 23 (:REWRITE MOD-X-Y-=-X . 4))
 (1826 23 (:REWRITE MOD-X-Y-=-X . 3))
 (1585 328 (:REWRITE DEFAULT-PLUS-1))
 (1563 762
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1524 762
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1488 339 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (1469 339
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1469 339
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1435 23 (:REWRITE MOD-ZERO . 4))
 (1201 135
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1149 339 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1149 339 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (1149 339
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (1117 1117 (:REWRITE REDUCE-INTEGERP-+))
 (1117 1117 (:REWRITE INTEGERP-MINUS-X))
 (1117 1117 (:META META-INTEGERP-CORRECT))
 (1102 1102 (:REWRITE THE-FLOOR-BELOW))
 (1102 1102 (:REWRITE THE-FLOOR-ABOVE))
 (1101 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (1095 221 (:REWRITE |(< 0 (/ x))|))
 (1043 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (943 762 (:REWRITE SIMPLIFY-SUMS-<))
 (904 904 (:REWRITE REDUCE-RATIONALP-+))
 (904 904 (:REWRITE RATIONALP-MINUS-X))
 (904 904 (:META META-RATIONALP-CORRECT))
 (825 21
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (825 21 (:REWRITE MOD-CANCEL-*-CONST))
 (762 762
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (762 762
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (762 762
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (762 762
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (762 762 (:REWRITE INTEGERP-<-CONSTANT))
 (762 762 (:REWRITE CONSTANT-<-INTEGERP))
 (762 762
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (762 762
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (762 762
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (762 762
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (762 762 (:REWRITE |(< c (- x))|))
 (762 762
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (762 762
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (762 762
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (762 762
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (762 762 (:REWRITE |(< (/ x) (/ y))|))
 (762 762 (:REWRITE |(< (- x) c)|))
 (762 762 (:REWRITE |(< (- x) (- y))|))
 (742 6 (:LINEAR MOD-BOUNDS-3))
 (705 139 (:REWRITE |(< (/ x) 0)|))
 (656 32 (:REWRITE |(equal (+ (- c) x) y)|))
 (611 339 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (611 339
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (520 115 (:REWRITE RTL::INTEGERP-FL))
 (474 12 (:DEFINITION RFIX))
 (455 60 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (429 227 (:REWRITE DEFAULT-MINUS))
 (410 169
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (370 16 (:REWRITE |(* (- x) y)|))
 (339 339 (:TYPE-PRESCRIPTION NATP))
 (339 339 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (339 339
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (339 339
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (334 334 (:REWRITE DEFAULT-EXPT-2))
 (321 321
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (299 299 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (279 17
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (248 17 (:REWRITE RTL::MOD-BY-1))
 (246 163 (:REWRITE |(equal (- x) (- y))|))
 (228 228
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (228 228
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (228 228
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (228 228
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (221 221
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (221 221
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (221 221 (:REWRITE |(< 0 (* x y))|))
 (218 37 (:REWRITE DEFAULT-MOD-2))
 (210 210
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (210 210
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (210 210
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (208 208 (:REWRITE |(expt 1/c n)|))
 (208 208 (:REWRITE |(expt (- x) n)|))
 (186 6 (:LINEAR RTL::MOD-BND-2))
 (169 169
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (163 163 (:REWRITE |(equal c (/ x))|))
 (163 163 (:REWRITE |(equal (/ x) (/ y))|))
 (162 15 (:REWRITE |(mod x 1)|))
 (139 139
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (139 139
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (139 139 (:REWRITE |(equal c (- x))|))
 (139 139 (:REWRITE |(< (* x y) 0)|))
 (135 135
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (134 22 (:REWRITE |(equal (expt x n) 0)|))
 (127 16 (:REWRITE |(integerp (- x))|))
 (115 37 (:REWRITE DEFAULT-MOD-1))
 (114 114 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (114 114 (:LINEAR EXPT-LINEAR-UPPER-<))
 (114 114 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (114 114 (:LINEAR EXPT-LINEAR-LOWER-<))
 (108 108 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (105 105
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (72 18 (:REWRITE |(integerp (expt x n))|))
 (54 54 (:LINEAR RTL::N<=FL-LINEAR))
 (42 42 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (33 18 (:REWRITE |(+ c (+ d x))|))
 (21 21
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (21 21 (:REWRITE |(mod x (- y))| . 3))
 (21 21 (:REWRITE |(mod x (- y))| . 2))
 (21 21 (:REWRITE |(mod x (- y))| . 1))
 (21 21 (:REWRITE |(mod (- x) y)| . 3))
 (21 21 (:REWRITE |(mod (- x) y)| . 2))
 (21 21 (:REWRITE |(mod (- x) y)| . 1))
 (17 17
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (17 17
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (17 17 (:REWRITE |(equal x (if a b c))|))
 (16 16
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (11 11
     (:REWRITE |(* (expt c m) (expt d n))|))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(equal (* x y) 0)|))
 (6 6 (:LINEAR RTL::MOD-BND-3))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3
    (:REWRITE |(equal (mod (+ x y) z) x)|)))
(RTL::CHOP-R-DOWN
 (253 27 (:REWRITE |(< c (- x))|))
 (141 19 (:REWRITE |(< (- x) c)|))
 (120
  120
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (120 120
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (120
     120
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (120 120
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (120 120
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (120 120
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (108 2 (:LINEAR EXPT->=-1-ONE))
 (106 2 (:LINEAR EXPT-<=-1-TWO))
 (106 2 (:LINEAR EXPT-<-1-TWO))
 (104 2 (:LINEAR EXPT->-1-ONE))
 (93 3 (:REWRITE RTL::INTEGERP-FL))
 (92 2 (:LINEAR EXPT-X->=-X))
 (92 2 (:LINEAR EXPT-X->-X))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (69 27 (:REWRITE DEFAULT-LESS-THAN-2))
 (57 15 (:REWRITE SIMPLIFY-SUMS-<))
 (57 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (57 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (50 50
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (47 8 (:REWRITE DEFAULT-TIMES-2))
 (45 8 (:REWRITE DEFAULT-TIMES-1))
 (27 27 (:REWRITE THE-FLOOR-BELOW))
 (27 27 (:REWRITE THE-FLOOR-ABOVE))
 (27 27
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (27 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (27 27
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (27 27 (:REWRITE DEFAULT-LESS-THAN-1))
 (27 27
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (27 27
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (27 27
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (27 27
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (27 27
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (27 27
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (27 27
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (27 27
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (27 27 (:REWRITE |(< (/ x) (/ y))|))
 (27 27 (:REWRITE |(< (- x) (- y))|))
 (15 15
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE DEFAULT-MINUS))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12 (:REWRITE |arith (expt x c)|))
 (12 12 (:REWRITE |arith (expt 1/c n)|))
 (12 12 (:REWRITE |(- (- x))|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 1 (:REWRITE DEFAULT-DIVIDE))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:REWRITE |arith (* c (* d x))|))
 (2 2 (:REWRITE |arith (* (- x) y)|))
 (2 2 (:LINEAR RTL::N<=FL-LINEAR))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |arith (- (* c x))|)))
(RTL::CHOP-R-MONOTONE
 (254 32 (:REWRITE DEFAULT-TIMES-2))
 (182 32 (:REWRITE DEFAULT-TIMES-1))
 (130
  130
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (130 130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (130
     130
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (130 130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (130 130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (130 130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (124 4 (:REWRITE RTL::INTEGERP-FL))
 (51 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (40 40
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (33 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (27 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (16 16 (:REWRITE DEFAULT-EXPT-2))
 (16 16 (:REWRITE DEFAULT-EXPT-1))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (12 8 (:REWRITE DEFAULT-PLUS-1))
 (9 5 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-PLUS-2))
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
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (4 4
    (:REWRITE |(* (expt c m) (expt d n))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::CHOP-R-CHOP-R
 (315 43 (:REWRITE DEFAULT-TIMES-2))
 (307 43 (:REWRITE DEFAULT-TIMES-1))
 (108
  108
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (108 108
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (108
     108
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (108 108
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (108 108
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (60 6 (:REWRITE DEFAULT-DIVIDE))
 (42 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (29 29 (:REWRITE DEFAULT-EXPT-2))
 (29 29 (:REWRITE DEFAULT-EXPT-1))
 (29 29 (:REWRITE |(expt 1/c n)|))
 (29 29 (:REWRITE |(expt (- x) n)|))
 (24 22 (:REWRITE DEFAULT-PLUS-1))
 (22 22 (:REWRITE DEFAULT-PLUS-2))
 (14 14 (:REWRITE DEFAULT-MINUS))
 (11 11 (:REWRITE REDUCE-INTEGERP-+))
 (11 11 (:REWRITE INTEGERP-MINUS-X))
 (11 11 (:META META-INTEGERP-CORRECT))
 (11 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 10
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (10 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (4 4
    (:REWRITE |(* (expt c m) (expt d n))|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE |(* c (* d x))|))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CHOP-R-SHIFT
 (564 106 (:REWRITE DEFAULT-TIMES-2))
 (528 106 (:REWRITE DEFAULT-TIMES-1))
 (434 29 (:REWRITE RTL::INTEGERP-FL))
 (377 377
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (377 377
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (377
     377
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (377 377
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (377 377
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (354 90 (:REWRITE DEFAULT-LESS-THAN-2))
 (350 350
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (350 350
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (320 40 (:REWRITE ACL2-NUMBERP-X))
 (274 12 (:LINEAR EXPT-<=-1-ONE))
 (265 12 (:LINEAR EXPT->=-1-TWO))
 (265 12 (:LINEAR EXPT->-1-TWO))
 (265 12 (:LINEAR EXPT-<-1-ONE))
 (260 84 (:REWRITE DEFAULT-LESS-THAN-1))
 (242 12 (:LINEAR EXPT-X->=-X))
 (242 12 (:LINEAR EXPT->=-1-ONE))
 (242 12 (:LINEAR EXPT-<=-1-TWO))
 (233 12 (:LINEAR EXPT-X->-X))
 (233 12 (:LINEAR EXPT->-1-ONE))
 (233 12 (:LINEAR EXPT-<-1-TWO))
 (208 52 (:REWRITE RATIONALP-X))
 (204 38
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (90 90 (:REWRITE THE-FLOOR-BELOW))
 (90 90 (:REWRITE THE-FLOOR-ABOVE))
 (90 90 (:REWRITE REDUCE-INTEGERP-+))
 (90 90 (:REWRITE INTEGERP-MINUS-X))
 (90 90 (:META META-INTEGERP-CORRECT))
 (87 9 (:REWRITE DEFAULT-DIVIDE))
 (80 80 (:REWRITE SIMPLIFY-SUMS-<))
 (80 80
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (80 80
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (80 80
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (80 80
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (80 80
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (80 80 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (80 80 (:REWRITE INTEGERP-<-CONSTANT))
 (80 80 (:REWRITE CONSTANT-<-INTEGERP))
 (80 80
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (80 80
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (80 80
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (80 80
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (80 80 (:REWRITE |(< c (- x))|))
 (80 80
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 80
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (80 80
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (80 80
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (80 80 (:REWRITE |(< (/ x) (/ y))|))
 (80 80 (:REWRITE |(< (- x) c)|))
 (80 80 (:REWRITE |(< (- x) (- y))|))
 (74 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (63 7 (:REWRITE |(equal (expt x n) 0)|))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (52 52 (:REWRITE REDUCE-RATIONALP-+))
 (52 52 (:REWRITE REDUCE-RATIONALP-*))
 (52 52 (:REWRITE RATIONALP-MINUS-X))
 (52 52 (:META META-RATIONALP-CORRECT))
 (46 46 (:REWRITE DEFAULT-EXPT-2))
 (46 38 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (44 38 (:REWRITE DEFAULT-PLUS-2))
 (42 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (42 42
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (42 42 (:REWRITE |(equal c (/ x))|))
 (42 42 (:REWRITE |(equal (/ x) (/ y))|))
 (42 42 (:REWRITE |(equal (- x) (- y))|))
 (42 38 (:REWRITE DEFAULT-PLUS-1))
 (41 41 (:REWRITE |(equal c (- x))|))
 (39 39
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (32 32 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (32 32 (:REWRITE |(expt 1/c n)|))
 (32 32 (:REWRITE |(expt (- x) n)|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< 0 (/ x))|))
 (24 24 (:REWRITE |(< 0 (* x y))|))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (20 20
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (20 20
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (20 20 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (18 18 (:REWRITE DEFAULT-MINUS))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:LINEAR RTL::N<=FL-LINEAR))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (5 5
    (:REWRITE |(* (expt c m) (expt d n))|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE |(equal x (if a b c))|)))
(RTL::CHOP-R-BOUND
 (884
  884
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (884 884
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (884
     884
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (884 884
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (884 884
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (433 67 (:REWRITE |(< (- x) c)|))
 (365 50 (:REWRITE DEFAULT-TIMES-2))
 (361 361
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (361 361
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (361 361
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (336 336
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (336 336
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (336 336
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (320 8 (:LINEAR EXPT-<-1-TWO))
 (258 54 (:REWRITE SIMPLIFY-SUMS-<))
 (239 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (235 67 (:REWRITE DEFAULT-LESS-THAN-1))
 (235 50 (:REWRITE DEFAULT-TIMES-1))
 (130 67 (:REWRITE DEFAULT-LESS-THAN-2))
 (123 43 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (100 100 (:REWRITE |arith (expt x c)|))
 (100 100 (:REWRITE |arith (expt 1/c n)|))
 (67 67 (:REWRITE THE-FLOOR-BELOW))
 (67 67 (:REWRITE THE-FLOOR-ABOVE))
 (67 67
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (67 67
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (67 67
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (67 67
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (67 67
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (67 67
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (67 67
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (67 67 (:REWRITE |(< c (- x))|))
 (67 67
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (67 67
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (67 67
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (67 67
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (67 67 (:REWRITE |(< (/ x) (/ y))|))
 (67 67 (:REWRITE |(< (- x) (- y))|))
 (66 8 (:LINEAR EXPT->-1-ONE))
 (58 8 (:LINEAR EXPT-X->=-X))
 (58 8 (:LINEAR EXPT-X->-X))
 (55 55
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (55 55 (:REWRITE INTEGERP-<-CONSTANT))
 (55 55 (:REWRITE CONSTANT-<-INTEGERP))
 (46 46 (:REWRITE REDUCE-INTEGERP-+))
 (46 46 (:REWRITE INTEGERP-MINUS-X))
 (46 46 (:META META-INTEGERP-CORRECT))
 (37 37 (:REWRITE DEFAULT-EXPT-2))
 (37 37 (:REWRITE DEFAULT-EXPT-1))
 (37 37 (:REWRITE |(expt 1/c n)|))
 (37 37 (:REWRITE |(expt (- x) n)|))
 (32 8 (:REWRITE RATIONALP-X))
 (30 3 (:REWRITE DEFAULT-DIVIDE))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 21 (:REWRITE DEFAULT-MINUS))
 (20 20 (:REWRITE |(< (/ x) 0)|))
 (20 20 (:REWRITE |(< (* x y) 0)|))
 (20 20 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (17 17 (:REWRITE |(< 0 (/ x))|))
 (17 17 (:REWRITE |(< 0 (* x y))|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 14 (:REWRITE |arith (* c (* d x))|))
 (14 14 (:REWRITE |arith (* (- x) y)|))
 (12 12 (:REWRITE |(- (- x))|))
 (12 8 (:REWRITE DEFAULT-PLUS-2))
 (10 10 (:LINEAR RTL::N<=FL-LINEAR))
 (10 8 (:REWRITE DEFAULT-PLUS-1))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:META META-RATIONALP-CORRECT))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:REWRITE |arith (- (* c x))|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2
    (:REWRITE |(* (expt c m) (expt d n))|)))
(RTL::CHOP-R-SMALL
 (1310 180 (:REWRITE |(< c (- x))|))
 (1087
  1087
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1087
      1087
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1087
     1087
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1087 1087
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1087 1087
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1087 1087
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (750 140 (:REWRITE |(< (- x) c)|))
 (664 14 (:LINEAR EXPT->=-1-ONE))
 (654 14 (:LINEAR EXPT-<=-1-TWO))
 (650 14 (:LINEAR EXPT-<-1-TWO))
 (640 14 (:LINEAR EXPT->-1-ONE))
 (607 28 (:REWRITE RTL::INTEGERP-FL))
 (564 14 (:LINEAR EXPT-X->=-X))
 (564 14 (:LINEAR EXPT-X->-X))
 (538 538
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (538 538
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (538 538
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (288 117
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (281 182 (:REWRITE DEFAULT-LESS-THAN-2))
 (281 182 (:REWRITE DEFAULT-LESS-THAN-1))
 (270 117
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (265 35 (:REWRITE DEFAULT-TIMES-2))
 (222 180
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (207 117 (:REWRITE SIMPLIFY-SUMS-<))
 (182 182 (:REWRITE THE-FLOOR-BELOW))
 (182 182 (:REWRITE THE-FLOOR-ABOVE))
 (180 180
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (180 180
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (180 180
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (180 180
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (180 180
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (180 180
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (180 180
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (180 180
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (180 180
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (180 180
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (180 180 (:REWRITE |(< (/ x) (/ y))|))
 (180 180 (:REWRITE |(< (- x) (- y))|))
 (152 89 (:REWRITE DEFAULT-MINUS))
 (129 35 (:REWRITE DEFAULT-TIMES-1))
 (120 120 (:REWRITE INTEGERP-<-CONSTANT))
 (120 120 (:REWRITE CONSTANT-<-INTEGERP))
 (64 64 (:REWRITE |(< (/ x) 0)|))
 (64 64 (:REWRITE |(< (* x y) 0)|))
 (60 60 (:REWRITE |(- (- x))|))
 (50 50 (:REWRITE REDUCE-INTEGERP-+))
 (50 50 (:REWRITE INTEGERP-MINUS-X))
 (50 50 (:META META-INTEGERP-CORRECT))
 (48 48 (:REWRITE |(< 0 (/ x))|))
 (48 48 (:REWRITE |(< 0 (* x y))|))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (44 44 (:REWRITE DEFAULT-EXPT-2))
 (44 44 (:REWRITE DEFAULT-EXPT-1))
 (44 44 (:REWRITE |(expt 1/c n)|))
 (44 44 (:REWRITE |(expt (- x) n)|))
 (44 11 (:REWRITE RATIONALP-X))
 (40 4 (:REWRITE DEFAULT-DIVIDE))
 (31 31
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (31 31
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (31 31
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (22 22 (:REWRITE |arith (expt x c)|))
 (22 22 (:REWRITE |arith (expt 1/c n)|))
 (22 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (15 11 (:REWRITE DEFAULT-PLUS-2))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (13 11 (:REWRITE DEFAULT-PLUS-1))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11 (:META META-RATIONALP-CORRECT))
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
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE |arith (* c (* d x))|))
 (2 2 (:REWRITE |arith (- (* c x))|))
 (2 2 (:REWRITE |arith (* (- x) y)|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2
    (:REWRITE |(* (expt c m) (expt d n))|))
 (1 1 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::CHOP-R-0
 (141 19 (:REWRITE DEFAULT-TIMES-1))
 (114
  114
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (114
     114
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (94 19 (:REWRITE DEFAULT-TIMES-2))
 (62 2 (:REWRITE RTL::INTEGERP-FL))
 (55 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (53 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (44 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (39 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38 38
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (12 8 (:REWRITE DEFAULT-PLUS-1))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 8 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE DEFAULT-PLUS-2))
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
 (8 6 (:REWRITE DEFAULT-MINUS))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4
    (:REWRITE |(* (expt c m) (expt d n))|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (4 1 (:REWRITE RATIONALP-X))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CHOP-R-INT-BOUNDS
 (40009 1 (:LINEAR RTL::MOD-BND-2))
 (6712 8 (:REWRITE RTL::CHOP-R-0))
 (5607
  5607
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5607
      5607
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5607
     5607
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5607 5607
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5607 5607
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5472 4 (:REWRITE |(< (if a b c) x)|))
 (4961 1559
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (4961 1559
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (4126 133 (:REWRITE RTL::INTEGERP-FL))
 (2625 582
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (1900 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1831 278 (:REWRITE DEFAULT-TIMES-2))
 (1674 278 (:REWRITE DEFAULT-TIMES-1))
 (1559 1559
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1482 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1434 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (1366 156
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1263 1263 (:REWRITE |arith (expt x c)|))
 (1258 1258 (:REWRITE |arith (expt 1/c n)|))
 (1167 128 (:REWRITE |(< (- x) c)|))
 (1006 119
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (994 142 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (994 142 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (899 22
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (799 190 (:REWRITE DEFAULT-PLUS-2))
 (786 3 (:REWRITE RTL::MOD-DOES-NOTHING))
 (756 3 (:REWRITE MOD-ZERO . 4))
 (703 47 (:REWRITE |(< 0 (/ x))|))
 (682 190 (:REWRITE DEFAULT-PLUS-1))
 (664 142
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (664 142
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (663 4
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (660 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (592 592
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (592 592
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (590 160 (:REWRITE DEFAULT-LESS-THAN-2))
 (582 582
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (538 121 (:REWRITE |arith (+ x x)|))
 (531 531
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (531 531
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (531 531
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (525 119
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (525 119
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (522 114 (:REWRITE CONSTANT-<-INTEGERP))
 (507 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (501 3 (:REWRITE CANCEL-MOD-+))
 (486 3 (:REWRITE MOD-X-Y-=-X . 4))
 (486 3 (:REWRITE MOD-X-Y-=-X . 3))
 (465 465
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (465 465
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (465 465
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (463 51
      (:REWRITE |arith (* (expt x m) (expt x n))|))
 (452 4 (:REWRITE |(* x (- y))|))
 (450 90
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (450 90
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (450 90
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (443 13 (:LINEAR EXPT-X->=-X))
 (443 13 (:LINEAR EXPT-X->-X))
 (398 398 (:REWRITE |arith (* c (* d x))|))
 (397 13 (:LINEAR EXPT-<-1-TWO))
 (392 244 (:REWRITE |arith (- (* c x))|))
 (380 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (370 96 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (370 74 (:REWRITE |arith (* x (- y))|))
 (365 160 (:REWRITE DEFAULT-LESS-THAN-1))
 (365 61 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (336 4 (:DEFINITION ABS))
 (302 23
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (297 3 (:REWRITE MOD-ZERO . 3))
 (284 284 (:REWRITE |arith (* (- x) y)|))
 (275 13 (:LINEAR EXPT->-1-ONE))
 (250 25 (:REWRITE DEFAULT-DIVIDE))
 (243 96 (:REWRITE SIMPLIFY-SUMS-<))
 (186 117 (:REWRITE DEFAULT-MINUS))
 (174 58 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (171 3 (:REWRITE DEFAULT-MOD-RATIO))
 (160 160 (:REWRITE THE-FLOOR-BELOW))
 (160 160 (:REWRITE THE-FLOOR-ABOVE))
 (142 142 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (142 142 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (142 142
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (142 142
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (142 142
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (141 15 (:REWRITE |(* (- x) y)|))
 (140 136 (:REWRITE |(< (- x) (- y))|))
 (138 3 (:REWRITE |(integerp (- x))|))
 (136 136
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (136 136
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (136 136
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (136 136
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (136 136
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (136 136
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (136 136
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (136 136
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (136 136
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (136 136
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (136 136 (:REWRITE |(< (/ x) (/ y))|))
 (133 133 (:REWRITE DEFAULT-EXPT-2))
 (133 133 (:REWRITE DEFAULT-EXPT-1))
 (133 133 (:REWRITE |(expt 1/c n)|))
 (133 133 (:REWRITE |(expt (- x) n)|))
 (128 128 (:REWRITE |(< c (- x))|))
 (121 121
      (:REWRITE |arith (* (expt c n) (expt d n))|))
 (116 58 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (110 110 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (108 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (108 3
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (107 107 (:REWRITE REDUCE-INTEGERP-+))
 (107 107 (:REWRITE INTEGERP-MINUS-X))
 (107 107 (:META META-INTEGERP-CORRECT))
 (106 106
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (106 106 (:REWRITE INTEGERP-<-CONSTANT))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4H-EXPT-C))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3H-EXPT-C))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2H-EXPT-C))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1H-EXPT-C))
 (88 88
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (81 3 (:REWRITE MOD-X-Y-=-X . 2))
 (78 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (78 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (67 67 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (58 58 (:TYPE-PRESCRIPTION NATP))
 (58 58 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (58 58
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (55 55 (:REWRITE |(< 0 (* x y))|))
 (55 55 (:LINEAR RTL::N<=FL-LINEAR))
 (51 3
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (51 3 (:REWRITE MOD-CANCEL-*-CONST))
 (51 3
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (51 3
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (50 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4G-EXPT-B))
 (50 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3G-EXPT-B))
 (50 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1G-EXPT-B))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (33 33 (:REWRITE |(< (* x y) 0)|))
 (31 22 (:REWRITE |(equal (- x) (- y))|))
 (30 3 (:REWRITE DEFAULT-MOD-2))
 (29 29 (:REWRITE |(< (/ x) 0)|))
 (29 29
     (:REWRITE |(* (expt c m) (expt d n))|))
 (28 28 (:TYPE-PRESCRIPTION ABS))
 (26 26
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (23 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal c (- x))|))
 (22 22 (:REWRITE |(equal (/ x) c)|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(* a (/ a) b)|))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 2 (:REWRITE |(- (+ x y))|))
 (15 15 (:REWRITE |(* c (* d x))|))
 (14 9 (:REWRITE |(+ c (+ d x))|))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (13 13 (:LINEAR EXPT->=-1-TWO))
 (13 13 (:LINEAR EXPT->-1-TWO))
 (13 13 (:LINEAR EXPT-<=-1-ONE))
 (13 13 (:LINEAR EXPT-<-1-ONE))
 (12 3 (:REWRITE RATIONALP-X))
 (11 1
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 8
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (8 8 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (8 8 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (8 8
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (8 8 (:REWRITE |(- (* c x))|))
 (8 4
    (:REWRITE |arith (+ (* c x) (* d x))|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 3 (:REWRITE DEFAULT-MOD-1))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2G-EXPT-B))
 (4 4 (:REWRITE |arith (* 0 x)|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3 3 (:REWRITE |(mod x (- y))| . 3))
 (3 3 (:REWRITE |(mod x (- y))| . 2))
 (3 3 (:REWRITE |(mod x (- y))| . 1))
 (3 3
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(mod (- x) y)| . 3))
 (3 3 (:REWRITE |(mod (- x) y)| . 2))
 (3 3 (:REWRITE |(mod (- x) y)| . 1))
 (3 3
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:LINEAR RTL::MOD-BND-3)))
(RTL::LEMMA1
 (4781 2 (:REWRITE RTL::CHOP-R-0))
 (3969 1 (:REWRITE |(< (if a b c) x)|))
 (3927 31
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3006 30 (:REWRITE RTL::INTEGERP-FL))
 (1823 50 (:REWRITE INTEGERP-MINUS-X))
 (1782 18 (:REWRITE RTL::FL+INT-REWRITE))
 (1350 18 (:REWRITE |(integerp (- x))|))
 (1297 41 (:REWRITE |(< (- x) c)|))
 (765 9 (:REWRITE |(integerp (expt x n))|))
 (696
  696
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (696 696
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (696
     696
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (696 696
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (696 696
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (668 87 (:REWRITE DEFAULT-TIMES-2))
 (632 83 (:REWRITE DEFAULT-MINUS))
 (608 87 (:REWRITE DEFAULT-TIMES-1))
 (356 178
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (283 57 (:REWRITE DEFAULT-PLUS-2))
 (209 57 (:REWRITE DEFAULT-PLUS-1))
 (187 23 (:REWRITE |(< 0 (/ x))|))
 (178 178
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (178 178
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (178 178
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (117 44 (:REWRITE DEFAULT-LESS-THAN-2))
 (111 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (103 44 (:REWRITE DEFAULT-LESS-THAN-1))
 (95 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (84 1 (:DEFINITION ABS))
 (81 81
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (81 81
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (81 81
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (64 64
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (64 64
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (64 64
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (64 64
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (52 52 (:REWRITE DEFAULT-EXPT-2))
 (52 52 (:REWRITE DEFAULT-EXPT-1))
 (52 52 (:REWRITE |(expt 1/c n)|))
 (52 52 (:REWRITE |(expt (- x) n)|))
 (44 44 (:REWRITE THE-FLOOR-BELOW))
 (44 44 (:REWRITE THE-FLOOR-ABOVE))
 (44 43 (:REWRITE |(< (- x) (- y))|))
 (43 43
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (43 43
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (43 43
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (43 43
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (43 43
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (43 43
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (43 43
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (43 43
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (43 43
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (43 43
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (43 43
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (43 43 (:REWRITE |(< (/ x) (/ y))|))
 (41 41 (:REWRITE REDUCE-INTEGERP-+))
 (41 41 (:REWRITE |(< c (- x))|))
 (41 41 (:META META-INTEGERP-CORRECT))
 (40 4 (:REWRITE DEFAULT-DIVIDE))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (31 31 (:REWRITE INTEGERP-<-CONSTANT))
 (31 31 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29 (:REWRITE SIMPLIFY-SUMS-<))
 (27 27 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (23 23 (:REWRITE |(< 0 (* x y))|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (13 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 10
     (:REWRITE |(* (expt c m) (expt d n))|))
 (10 10 (:LINEAR RTL::FL-MONOTONE-LINEAR))
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
 (8 2 (:REWRITE RATIONALP-X))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(- (* c x))|))
 (5 5 (:LINEAR RTL::N<=FL-LINEAR))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3 3
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (3 3
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::LEMMA2
 (7301 284 (:REWRITE INTEGERP-MINUS-X))
 (7243 111 (:REWRITE |(integerp (- x))|))
 (7192 66 (:REWRITE RTL::FL+INT-REWRITE))
 (5583
  5583
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5583
      5583
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5583
     5583
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5583 5583
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5583 5583
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3825 45 (:REWRITE |(integerp (expt x n))|))
 (3696 4 (:REWRITE RTL::CHOP-R-0))
 (3565 1576
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3565 1576
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3214 1333
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3214 1333
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2871 234 (:REWRITE |(< (- x) c)|))
 (2842 159
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2832 2 (:REWRITE |(< (if a b c) x)|))
 (2561 445 (:REWRITE DEFAULT-MINUS))
 (2307 280 (:REWRITE DEFAULT-TIMES-2))
 (1792 1576
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1584 280 (:REWRITE DEFAULT-TIMES-1))
 (1391 251 (:META META-INTEGERP-CORRECT))
 (1333 1333
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (1151 248 (:REWRITE DEFAULT-PLUS-2))
 (756 14 (:LINEAR EXPT->=-1-ONE))
 (752 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (747 248 (:REWRITE DEFAULT-PLUS-1))
 (742 14 (:LINEAR EXPT-<-1-TWO))
 (721 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (721 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (534 534 (:REWRITE |arith (expt x c)|))
 (527 527 (:REWRITE |arith (expt 1/c n)|))
 (526 526
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (526 526
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (526 526
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (456 128 (:REWRITE |(< 0 (/ x))|))
 (386 240 (:REWRITE DEFAULT-LESS-THAN-2))
 (331 240 (:REWRITE DEFAULT-LESS-THAN-1))
 (328 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (301 301 (:REWRITE |arith (* c (* d x))|))
 (297 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (297 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (278 48 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (260 155
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (251 251 (:REWRITE REDUCE-INTEGERP-+))
 (240 240 (:REWRITE THE-FLOOR-BELOW))
 (240 240 (:REWRITE THE-FLOOR-ABOVE))
 (240 238 (:REWRITE |(< (- x) (- y))|))
 (238 238
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (238 238
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (238 238
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (238 238
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (238 238
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (238 238
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (238 238
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (238 238
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (238 238
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (238 238
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (238 238
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (238 238 (:REWRITE |(< (/ x) (/ y))|))
 (236 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4H-EXPT-C))
 (236 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2H-EXPT-C))
 (234 234 (:REWRITE |(< c (- x))|))
 (218 218 (:REWRITE DEFAULT-EXPT-2))
 (218 218 (:REWRITE DEFAULT-EXPT-1))
 (218 218 (:REWRITE |(expt 1/c n)|))
 (218 218 (:REWRITE |(expt (- x) n)|))
 (218 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3H-EXPT-C))
 (218 200
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1H-EXPT-C))
 (188 188
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (168 2 (:DEFINITION ABS))
 (160 160 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (159 159
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (159 159 (:REWRITE INTEGERP-<-CONSTANT))
 (159 159 (:REWRITE CONSTANT-<-INTEGERP))
 (155 155 (:REWRITE SIMPLIFY-SUMS-<))
 (142 142 (:REWRITE |arith (* (- x) y)|))
 (137 137 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (128 128 (:REWRITE |(< 0 (* x y))|))
 (124 124
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (124 124
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (100 100 (:REWRITE |(< (/ x) 0)|))
 (100 100 (:REWRITE |(< (* x y) 0)|))
 (80 80 (:LINEAR RTL::N<=FL-LINEAR))
 (80 8 (:REWRITE DEFAULT-DIVIDE))
 (66 66
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (53 34 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (44 44 (:REWRITE |(- (* c x))|))
 (44 11 (:REWRITE RATIONALP-X))
 (43 42 (:REWRITE |(equal (- x) (- y))|))
 (42 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (42 42
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (42 42
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (42 42 (:REWRITE |(equal c (/ x))|))
 (42 42 (:REWRITE |(equal c (- x))|))
 (42 42 (:REWRITE |(equal (/ x) c)|))
 (42 42 (:REWRITE |(equal (/ x) (/ y))|))
 (42 42 (:REWRITE |(equal (- x) c)|))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26
     (:REWRITE |arith (* (expt c n) (expt d n))|))
 (25 25 (:REWRITE |(equal (+ (- c) x) y)|))
 (25 25
     (:REWRITE |(* (expt c m) (expt d n))|))
 (14 14 (:LINEAR EXPT-X->=-X))
 (14 14 (:LINEAR EXPT-X->-X))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT->-1-ONE))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11 (:META META-RATIONALP-CORRECT))
 (9 9 (:REWRITE |(* c (* d x))|))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7 7
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (7 7
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::CHOP-R-INT-NEG
 (1080 8 (:REWRITE RTL::CHOP-R-0))
 (652 4 (:REWRITE |(< (if a b c) x)|))
 (439
  439
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (439 439
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (439
     439
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (439 439
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (439 439
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (412 16 (:REWRITE RTL::INTEGERP-FL))
 (284 34 (:REWRITE DEFAULT-PLUS-2))
 (228 34 (:REWRITE DEFAULT-PLUS-1))
 (150 20 (:REWRITE DEFAULT-TIMES-2))
 (148 4 (:DEFINITION ABS))
 (140 36 (:REWRITE DEFAULT-MINUS))
 (132 8
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (126 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (100 100
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (100 100
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (100 100
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (100 100
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (95 95
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (90 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (90 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (86 14 (:REWRITE SIMPLIFY-SUMS-<))
 (74 20 (:REWRITE DEFAULT-TIMES-1))
 (42 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (20 20
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE DEFAULT-EXPT-1))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (16 16
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (14 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (14 14 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE CONSTANT-<-INTEGERP))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< c (- x))|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (14 14 (:REWRITE |(< (- x) (- y))|))
 (10 4 (:REWRITE RATIONALP-X))
 (8 8 (:TYPE-PRESCRIPTION ABS))
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
 (8 8 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:REWRITE |(- (- x))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (4 4 (:LINEAR RTL::N<=FL-LINEAR))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::CHOP
 (11
   11
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (11
  11
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::|chop as chop-r|
 (78 18 (:REWRITE DEFAULT-TIMES-1))
 (62 2 (:REWRITE RTL::INTEGERP-FL))
 (40 4 (:REWRITE DEFAULT-DIVIDE))
 (33 4 (:REWRITE ACL2-NUMBERP-X))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (22
   22
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (22
  22
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (17 5 (:REWRITE RATIONALP-X))
 (14 14 (:REWRITE REDUCE-INTEGERP-+))
 (14 14 (:REWRITE INTEGERP-MINUS-X))
 (14 14 (:META META-INTEGERP-CORRECT))
 (9 1 (:REWRITE RTL::CHOP-R-0))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-MINUS)))
(RTL::CHOP-MOD
 (14053 2 (:REWRITE RTL::CHOP-R-0))
 (6477 1 (:REWRITE |(< (if a b c) x)|))
 (6071 120
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3087 1 (:DEFINITION ABS))
 (2549
  2549
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2549
      2549
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2549
     2549
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2549 2549
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2549 2549
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2385 18 (:REWRITE CANCEL-MOD-+))
 (2301 18 (:REWRITE RTL::MOD-DOES-NOTHING))
 (2116 217 (:REWRITE DEFAULT-TIMES-2))
 (1723 40 (:REWRITE DEFAULT-PLUS-2))
 (1442 18 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1414 163 (:REWRITE DEFAULT-LESS-THAN-1))
 (1372 10
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1353 147 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1341 147
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1341 147
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1302 147 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (1208 18 (:REWRITE MOD-ZERO . 3))
 (1200 120
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1155 147 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1155 147 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (1155 147
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (1150 25 (:REWRITE |(* (* x y) z)|))
 (1142 2 (:REWRITE |(+ y (+ x z))|))
 (1117 18 (:REWRITE MOD-X-Y-=-X . 4))
 (1117 18 (:REWRITE MOD-X-Y-=-X . 3))
 (1103 18 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1081 217 (:REWRITE DEFAULT-TIMES-1))
 (954 18 (:REWRITE DEFAULT-MOD-RATIO))
 (953 162 (:REWRITE |(< c (- x))|))
 (949 40 (:REWRITE DEFAULT-PLUS-1))
 (926 16 (:REWRITE ODD-EXPT-THM))
 (879 18 (:REWRITE MOD-ZERO . 4))
 (837 18 (:REWRITE |(* (- x) y)|))
 (832 115 (:REWRITE DEFAULT-MINUS))
 (672 134 (:REWRITE |(< (- x) c)|))
 (619 163 (:REWRITE DEFAULT-LESS-THAN-2))
 (594 117 (:REWRITE SIMPLIFY-SUMS-<))
 (558 18 (:REWRITE |(integerp (- x))|))
 (477 18 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (477 18
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (396 18 (:REWRITE MOD-X-Y-=-X . 2))
 (384 162 (:REWRITE |(< (- x) (- y))|))
 (381 10 (:LINEAR EXPT->=-1-ONE))
 (374 10 (:LINEAR EXPT-<=-1-TWO))
 (374 10 (:LINEAR EXPT-<-1-TWO))
 (367 10 (:LINEAR EXPT->-1-ONE))
 (360 36 (:REWRITE DEFAULT-DIVIDE))
 (359 4 (:REWRITE |(+ y x)|))
 (341 1 (:REWRITE |(- (+ x y))|))
 (325 10 (:LINEAR EXPT-X->=-X))
 (325 10 (:LINEAR EXPT-X->-X))
 (324 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (315 18 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (315 18 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (309 147 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (247 247
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (247 247
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (247 247
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (247 247
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (227 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (226 4 (:REWRITE |(+ 0 x)|))
 (219 9 (:REWRITE RTL::MOD-BY-1))
 (219 9 (:REWRITE |(mod x 1)|))
 (210 18
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (186 18 (:REWRITE MOD-CANCEL-*-CONST))
 (181 70 (:REWRITE |(- (- x))|))
 (170 59 (:REWRITE INTEGERP-MINUS-X))
 (168 2 (:LINEAR MOD-BOUNDS-3))
 (163 163 (:REWRITE THE-FLOOR-BELOW))
 (163 163 (:REWRITE THE-FLOOR-ABOVE))
 (162 162
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (162 162
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (162 162
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (162 162
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (162 162
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (162 162
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (162 162
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (162 162
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (162 162
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (162 162
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (162 162
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (162 162 (:REWRITE |(< (/ x) (/ y))|))
 (147 147 (:TYPE-PRESCRIPTION NATP))
 (147 147 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (147 147 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (147 147
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (147 147
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (147 147
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (120 120
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (120 120 (:REWRITE INTEGERP-<-CONSTANT))
 (120 120 (:REWRITE CONSTANT-<-INTEGERP))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (100 4 (:LINEAR MOD-BOUNDS-2))
 (99 18 (:REWRITE DEFAULT-MOD-2))
 (99 18 (:REWRITE DEFAULT-MOD-1))
 (81 9
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (77 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (77 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (62 2 (:LINEAR RTL::MOD-BND-2))
 (60 60 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (59 59 (:REWRITE REDUCE-INTEGERP-+))
 (59 59 (:REWRITE |(< (/ x) 0)|))
 (59 59 (:REWRITE |(< (* x y) 0)|))
 (59 59 (:META META-INTEGERP-CORRECT))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (42 42 (:REWRITE |(< 0 (/ x))|))
 (42 42 (:REWRITE |(< 0 (* x y))|))
 (42 18
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (40 40 (:REWRITE DEFAULT-EXPT-2))
 (40 40 (:REWRITE DEFAULT-EXPT-1))
 (40 40 (:REWRITE |(expt 1/c n)|))
 (40 40 (:REWRITE |(expt (- x) n)|))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (21 21 (:REWRITE |(- (* c x))|))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (20 20
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (18 18 (:REWRITE |(mod x (- y))| . 3))
 (18 18 (:REWRITE |(mod x (- y))| . 2))
 (18 18 (:REWRITE |(mod x (- y))| . 1))
 (18 18 (:REWRITE |(mod (- x) y)| . 3))
 (18 18 (:REWRITE |(mod (- x) y)| . 2))
 (18 18 (:REWRITE |(mod (- x) y)| . 1))
 (18 9
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (14 14
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (10 10 (:LINEAR EXPT->=-1-TWO))
 (10 10 (:LINEAR EXPT->-1-TWO))
 (10 10 (:LINEAR EXPT-<=-1-ONE))
 (10 10 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:REWRITE |(equal (* x y) 0)|))
 (7 7
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:LINEAR RTL::MOD-BND-3))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CHOP-DOWN)
(RTL::CHOP-MONOTONE)
(RTL::CHOP-CHOP
 (566 10 (:REWRITE RTL::CHOP-R-0))
 (348 2 (:REWRITE |(< (if a b c) x)|))
 (74 2 (:DEFINITION ABS))
 (64 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (46 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (46 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (44 8 (:REWRITE SIMPLIFY-SUMS-<))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (32
   32
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (32
  32
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (22 4 (:REWRITE ODD-EXPT-THM))
 (18 3 (:REWRITE RATIONALP-X))
 (16 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 2 (:REWRITE |(integerp (- x))|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::CHOP-SHIFT
 (14
   14
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::CHOP-BOUND
 (532 4 (:REWRITE RTL::CHOP-R-0))
 (348 2 (:REWRITE |(< (if a b c) x)|))
 (74 2 (:DEFINITION ABS))
 (66 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (51 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (50 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (49 10 (:REWRITE SIMPLIFY-SUMS-<))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (32
   32
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (32
  32
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (22 4 (:REWRITE ODD-EXPT-THM))
 (21 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
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
 (10 2 (:REWRITE |(integerp (- x))|))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::CHOP-SMALL
 (804 2 (:REWRITE RTL::CHOP-R-0))
 (599 2 (:REWRITE |(< (if a b c) x)|))
 (275 23 (:REWRITE |(< (- x) c)|))
 (256 1 (:DEFINITION ABS))
 (223 31 (:REWRITE |(< (- x) (- y))|))
 (169
  169
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (169
     169
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (140 27 (:REWRITE |(< c (- x))|))
 (139 3 (:REWRITE ODD-EXPT-THM))
 (112 9 (:REWRITE |(< 0 (/ x))|))
 (111 18 (:REWRITE SIMPLIFY-SUMS-<))
 (90 27 (:REWRITE DEFAULT-MINUS))
 (88 1
     (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (87 33 (:REWRITE DEFAULT-LESS-THAN-2))
 (85 1 (:REWRITE |(integerp (expt x n))|))
 (78 33 (:REWRITE DEFAULT-LESS-THAN-1))
 (64 1
     (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
 (64 1
     (:REWRITE |(< (expt x n) (expt x m))|))
 (60 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 6 (:REWRITE |(+ y x)|))
 (54 1 (:LINEAR EXPT->=-1-ONE))
 (53 1 (:LINEAR EXPT-<=-1-TWO))
 (53 1 (:LINEAR EXPT-<-1-TWO))
 (52 1 (:LINEAR EXPT->-1-ONE))
 (46 1 (:LINEAR EXPT-X->=-X))
 (46 1 (:LINEAR EXPT-X->-X))
 (45 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (42 6 (:REWRITE NORMALIZE-ADDENDS))
 (37 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (34 16 (:REWRITE |(- (- x))|))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (31 31
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (31 31 (:REWRITE |(< (/ x) (/ y))|))
 (29 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (28 28
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (28 28
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (28 28
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (24 18 (:REWRITE DEFAULT-PLUS-1))
 (21 1 (:REWRITE |(- (if a b c))|))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (19 19 (:REWRITE CONSTANT-<-INTEGERP))
 (18 18 (:REWRITE DEFAULT-PLUS-2))
 (16 2 (:REWRITE |(equal (/ x) c)|))
 (12 6 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (11 2 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:DEFINITION FIX))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 1 (:REWRITE |(/ (expt x n))|))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(+ x (- x))|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(/ (/ x))|))
 (1 1 (:META META-RATIONALP-CORRECT))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::CHOP-0
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
 (84 84
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (84 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (64 10 (:REWRITE SIMPLIFY-SUMS-<))
 (64 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (64 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (39 6 (:REWRITE ODD-EXPT-THM))
 (15 3 (:REWRITE |(integerp (- x))|))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
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
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (7 7 (:REWRITE DEFAULT-MINUS))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 1 (:REWRITE RATIONALP-X))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::CHOP-INT-BOUNDS
 (144
  144
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (144
     144
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (60 60
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (60 60
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (60 60
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (12 12
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (12 12
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::CHOP-INT-NEG
 (88 4 (:REWRITE RTL::INTEGERP-FL))
 (33
  33
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (33 33
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (33 33
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (33 33
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (33 33
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (4 2 (:REWRITE DEFAULT-PLUS-2))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR RTL::N<=FL-LINEAR)))
