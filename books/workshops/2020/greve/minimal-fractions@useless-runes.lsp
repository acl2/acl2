(NATP-NFIX (2 2 (:REWRITE DEFAULT-<-2))
           (2 2 (:REWRITE DEFAULT-<-1)))
(NFIX-EQUIV)
(NFIX-EQUIV-IS-AN-EQUIVALENCE)
(NFIX-EQUIV-NFIX (3 3 (:REWRITE DEFAULT-<-2))
                 (3 3 (:REWRITE DEFAULT-<-1))
                 (3 1 (:DEFINITION NATP))
                 (1 1 (:TYPE-PRESCRIPTION NATP)))
(NFIX-EQUIV-IMPLIES-EQUAL-NFIX-1)
(IFIX-EQUIV)
(IFIX-EQUIV-IS-AN-EQUIVALENCE)
(IFIX-EQUIV-IFIX)
(IFIX-EQUIV-IMPLIES-EQUAL-IFIX-1)
(PFIX)
(POSP-PFIX-IDENTITY (1 1 (:REWRITE DEFAULT-<-2))
                    (1 1 (:REWRITE DEFAULT-<-1)))
(POSP-PFIX)
(POSP-IMPLIES)
(PFIX-EQUIV)
(PFIX-EQUIV-IS-AN-EQUIVALENCE)
(PFIX-EQUIV-PFIX (3 3 (:REWRITE DEFAULT-<-2))
                 (3 3 (:REWRITE DEFAULT-<-1))
                 (1 1 (:TYPE-PRESCRIPTION POSP)))
(PFIX-EQUIV-IMPLIES-EQUAL-PFIX-1)
(NEGP)
(NEG-FIX (1 1 (:TYPE-PRESCRIPTION NEG-FIX)))
(NEG-EQUIV (10 10 (:TYPE-PRESCRIPTION NEG-FIX)))
(NEGP-NEG-FIX (2 2 (:REWRITE DEFAULT-<-2))
              (2 2 (:REWRITE DEFAULT-<-1)))
(NEG-EQUIV-IS-AN-EQUIVALENCE (6 6 (:TYPE-PRESCRIPTION NEG-FIX)))
(NEGP-IMPLIES)
(NON-TRIVIAL-MODULUS)
(PMOD (25 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
      (25 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
      (25 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
      (25 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
      (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
      (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
      (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
      (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
      (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
      (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
      (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
      (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
      (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(T-T-IMPLIES-NATP-PMOD)
(PMOD)
(MOD-PMOD (4960 4 (:REWRITE |(mod (mod x y) z)| . 1))
          (4659 50 (:REWRITE MOD-X-Y-=-X . 4))
          (4499 50 (:REWRITE MOD-X-Y-=-X-Y . 2))
          (4486 50 (:REWRITE MOD-ZERO . 4))
          (3990 3990
                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (3990 3990
                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (3990 3990
                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (3802 49 (:REWRITE CANCEL-MOD-+))
          (2655 531 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
          (2655 531 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
          (2631 531
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
          (2631 531
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
          (2167 155
                (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
          (2107 263 (:REWRITE DEFAULT-TIMES-2))
          (1424 53 (:REWRITE |(integerp (- x))|))
          (1272 50 (:REWRITE MOD-ZERO . 3))
          (1158 50 (:REWRITE DEFAULT-MOD-RATIO))
          (1085 53 (:REWRITE |(* (- x) y)|))
          (1011 263 (:REWRITE DEFAULT-TIMES-1))
          (864 4 (:REWRITE |(* (* x y) z)|))
          (815 50 (:REWRITE MOD-X-Y-=-X+Y . 2))
          (737 49 (:REWRITE |(mod (+ x (mod a b)) y)|))
          (712 57 (:REWRITE |(* y x)|))
          (645 49
               (:REWRITE |(mod (+ x (- (mod a b))) y)|))
          (613 49 (:REWRITE MOD-X-Y-=-X . 2))
          (544 24 (:LINEAR MOD-BOUNDS-3))
          (531 531 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
          (531 531
               (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
          (531 531
               (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
          (531 531
               (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
          (531 531 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
          (517 89 (:META META-INTEGERP-CORRECT))
          (515 55
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
          (515 55 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
          (494 50 (:REWRITE MOD-X-Y-=-X-Y . 3))
          (494 50 (:REWRITE MOD-X-Y-=-X+Y . 3))
          (457 53 (:REWRITE DEFAULT-MINUS))
          (456 48 (:LINEAR MOD-BOUNDS-2))
          (425 49 (:REWRITE MOD-CANCEL-*-CONST))
          (368 4 (:REWRITE FLOOR-ZERO . 3))
          (359 55 (:REWRITE DEFAULT-LESS-THAN-1))
          (331 55 (:REWRITE SIMPLIFY-SUMS-<))
          (269 49
               (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
          (269 49
               (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
          (269 49
               (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
          (252 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
          (252 28
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
          (252 28
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
          (252 28
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
          (252 28
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
          (230 50 (:REWRITE DEFAULT-MOD-1))
          (225 141 (:REWRITE DEFAULT-DIVIDE))
          (224 4 (:REWRITE CANCEL-FLOOR-+))
          (211 55 (:REWRITE DEFAULT-LESS-THAN-2))
          (209 49
               (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
          (209 49
               (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
          (209 49
               (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
          (196 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
          (196 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
          (176 4 (:REWRITE FLOOR-ZERO . 5))
          (176 4 (:REWRITE FLOOR-ZERO . 4))
          (176 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
          (158 10
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (158 10
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (155 155
               (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
          (155 155
               (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
          (155 155
               (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
          (149 149
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
          (141 141
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
          (140 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
          (140 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
          (140 28
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
          (120 4 (:REWRITE FLOOR-=-X/Y . 3))
          (120 4 (:REWRITE FLOOR-=-X/Y . 2))
          (89 89 (:REWRITE REDUCE-INTEGERP-+))
          (89 89 (:REWRITE INTEGERP-MINUS-X))
          (82 50 (:REWRITE DEFAULT-MOD-2))
          (69 5 (:REWRITE MOD-ZERO . 1))
          (61 5 (:REWRITE MOD-POSITIVE . 3))
          (60 4 (:REWRITE DEFAULT-FLOOR-RATIO))
          (55 55 (:REWRITE THE-FLOOR-BELOW))
          (55 55 (:REWRITE THE-FLOOR-ABOVE))
          (55 55
              (:REWRITE REMOVE-STRICT-INEQUALITIES))
          (55 55
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
          (55 55
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
          (55 55
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
          (55 55 (:REWRITE INTEGERP-<-CONSTANT))
          (55 55 (:REWRITE CONSTANT-<-INTEGERP))
          (55 55
              (:REWRITE |(< c (/ x)) positive c --- present in goal|))
          (55 55
              (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
          (55 55
              (:REWRITE |(< c (/ x)) negative c --- present in goal|))
          (55 55
              (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
          (55 55 (:REWRITE |(< c (- x))|))
          (55 55
              (:REWRITE |(< (/ x) c) positive c --- present in goal|))
          (55 55
              (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
          (55 55
              (:REWRITE |(< (/ x) c) negative c --- present in goal|))
          (55 55
              (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
          (55 55 (:REWRITE |(< (/ x) (/ y))|))
          (55 55 (:REWRITE |(< (- x) c)|))
          (55 55 (:REWRITE |(< (- x) (- y))|))
          (53 53 (:REWRITE |(- (* c x))|))
          (49 49 (:REWRITE |(mod x (- y))| . 3))
          (49 49 (:REWRITE |(mod x (- y))| . 2))
          (49 49 (:REWRITE |(mod x (- y))| . 1))
          (49 49 (:REWRITE |(mod (- x) y)| . 3))
          (49 49 (:REWRITE |(mod (- x) y)| . 2))
          (49 49 (:REWRITE |(mod (- x) y)| . 1))
          (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
          (41 5 (:REWRITE MOD-ZERO . 2))
          (37 5 (:REWRITE MOD-NONPOSITIVE))
          (32 4 (:REWRITE FLOOR-ZERO . 2))
          (32 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
          (32 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
          (28 28 (:TYPE-PRESCRIPTION FLOOR))
          (28 4
              (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
          (28 4 (:REWRITE FLOOR-CANCEL-*-CONST))
          (28 4
              (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
          (28 4
              (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
          (26 22 (:REWRITE |(< (/ x) 0)|))
          (22 22
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (22 22
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (22 22 (:REWRITE |(< (* x y) 0)|))
          (15 15
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
          (15 15
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
          (15 15 (:REWRITE |(< 0 (/ x))|))
          (15 15 (:REWRITE |(< 0 (* x y))|))
          (13 5
              (:REWRITE |(equal (mod (+ x y) z) x)|))
          (10 10
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
          (9 5 (:REWRITE MOD-POSITIVE . 2))
          (8 4 (:REWRITE DEFAULT-FLOOR-2))
          (8 4 (:REWRITE DEFAULT-FLOOR-1))
          (5 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
          (5 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
          (5 5 (:REWRITE MOD-POSITIVE . 1))
          (4 4 (:REWRITE INTEGERP-/))
          (4 4
             (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
          (4 4 (:REWRITE |(mod (mod x y) z)| . 3))
          (4 4 (:REWRITE |(mod (mod x y) z)| . 2))
          (4 4 (:REWRITE |(floor x (- y))| . 2))
          (4 4 (:REWRITE |(floor x (- y))| . 1))
          (4 4
             (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
          (4 4 (:REWRITE |(floor (- x) y)| . 2))
          (4 4 (:REWRITE |(floor (- x) y)| . 1))
          (4 4
             (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
          (4 4
             (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
          (4 4
             (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
          (4 4 (:REWRITE |(* c (* d x))|)))
(PMOD-ZERO)
(PMOD-BOUND
     (289 289
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (289 289
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (289 289
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (225 45 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (225 45 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (225 45
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (225 45
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (202 4 (:REWRITE CANCEL-MOD-+))
     (160 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (160 4 (:REWRITE MOD-X-Y-=-X . 4))
     (160 4 (:REWRITE MOD-X-Y-=-X . 3))
     (156 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (110 4 (:REWRITE MOD-ZERO . 3))
     (92 4 (:REWRITE MOD-ZERO . 4))
     (82 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (81 6 (:REWRITE DEFAULT-MOD-RATIO))
     (76 4 (:REWRITE |(integerp (- x))|))
     (57 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (57 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (55 2 (:LINEAR MOD-BOUNDS-3))
     (54 4 (:REWRITE |(* (- x) y)|))
     (51 19 (:REWRITE SIMPLIFY-SUMS-<))
     (45 45 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (45 45
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (45 45 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (45 45
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (45 45 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (39 30 (:REWRITE DEFAULT-TIMES-2))
     (39 30 (:REWRITE DEFAULT-TIMES-1))
     (32 8 (:REWRITE |(* y x)|))
     (30 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (30 4
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (28 4 (:REWRITE MOD-X-Y-=-X . 2))
     (26 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (26 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (26 4 (:LINEAR MOD-BOUNDS-2))
     (24 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (24 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (24 4 (:REWRITE MOD-CANCEL-*-CONST))
     (24 4 (:REWRITE DEFAULT-MINUS))
     (24 4
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (24 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (23 16 (:REWRITE DEFAULT-DIVIDE))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (19 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (19 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19 (:REWRITE INTEGERP-<-CONSTANT))
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
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (15 15
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 1 (:REWRITE |(* (if a b c) x)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 6 (:REWRITE DEFAULT-MOD-2))
     (8 6 (:REWRITE DEFAULT-MOD-1))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
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
     (4 4 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE |(* 0 x)|)))
(NMOD (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
      (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
      (20 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
      (20 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
      (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
      (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
      (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
      (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
      (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
      (4 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
      (4 4 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
      (4 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
      (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(T-T-IMPLIES-NEGP-NMOD
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (151 43 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (151 43 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (151 43
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (151 43
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (129 17 (:REWRITE DEFAULT-LESS-THAN-1))
     (125 12 (:REWRITE DEFAULT-PLUS-1))
     (124 12 (:REWRITE DEFAULT-PLUS-2))
     (101 7 (:REWRITE DEFAULT-MOD-RATIO))
     (84 2 (:REWRITE CANCEL-MOD-+))
     (70 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (70 2 (:REWRITE MOD-X-Y-=-X . 4))
     (70 2 (:REWRITE MOD-X-Y-=-X . 3))
     (68 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (62 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (48 12 (:REWRITE |(* y x)|))
     (48 2 (:REWRITE MOD-ZERO . 3))
     (43 43 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (43 43
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (43 43 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (43 43
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (43 43 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (41 13 (:REWRITE SIMPLIFY-SUMS-<))
     (36 2 (:REWRITE POSP-PFIX-IDENTITY))
     (36 2 (:REWRITE MOD-ZERO . 4))
     (34 34 (:REWRITE DEFAULT-TIMES-2))
     (34 34 (:REWRITE DEFAULT-TIMES-1))
     (34 4 (:REWRITE |(* (if a b c) x)|))
     (32 2 (:REWRITE |(integerp (- x))|))
     (26 2 (:REWRITE |(* (- x) y)|))
     (24 1 (:LINEAR MOD-BOUNDS-3))
     (22 1 (:REWRITE |(* x (if a b c))|))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (17 17 (:REWRITE THE-FLOOR-BELOW))
     (17 17 (:REWRITE THE-FLOOR-ABOVE))
     (17 17 (:REWRITE DEFAULT-LESS-THAN-2))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< c (- x))|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 15 (:REWRITE |(< (- x) (- y))|))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE CONSTANT-<-INTEGERP))
     (13 5 (:REWRITE DEFAULT-MINUS))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11 (:REWRITE DEFAULT-DIVIDE))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (10 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (10 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (10 2 (:REWRITE MOD-X-Y-=-X . 2))
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
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE DEFAULT-MOD-2))
     (7 7 (:REWRITE DEFAULT-MOD-1))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(* 1 x)|))
     (3 3 (:REWRITE |(* 0 x)|))
     (3 1 (:REWRITE |(/ (if a b c))|))
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
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(- (* c x))|))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(NMOD (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
      (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
      (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
      (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
      (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
      (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
      (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
      (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
      (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
      (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
      (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
      (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
      (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(NMOD-REDUCTION
     (346 346
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (346 346
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (346 346
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (314 6 (:REWRITE CANCEL-MOD-+))
     (258 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (250 6 (:REWRITE MOD-X-Y-=-X . 4))
     (250 6 (:REWRITE MOD-X-Y-=-X . 3))
     (244 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (238 14 (:REWRITE DEFAULT-PLUS-1))
     (222 62 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (222 62 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (222 62
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (222 62
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (218 16 (:REWRITE DEFAULT-MOD-RATIO))
     (166 6 (:REWRITE MOD-ZERO . 3))
     (148 6 (:REWRITE MOD-ZERO . 4))
     (120 6 (:REWRITE |(integerp (- x))|))
     (76 58 (:REWRITE DEFAULT-TIMES-2))
     (76 58 (:REWRITE DEFAULT-TIMES-1))
     (76 6 (:REWRITE |(* (- x) y)|))
     (70 14 (:REWRITE DEFAULT-PLUS-2))
     (62 62 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (62 62
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (62 62 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (62 62
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (62 62 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (62 2 (:LINEAR MOD-BOUNDS-3))
     (56 8 (:REWRITE |(* (if a b c) x)|))
     (50 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (50 6
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (49 29
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (49 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (46 6 (:REWRITE MOD-X-Y-=-X . 2))
     (42 28 (:REWRITE DEFAULT-DIVIDE))
     (42 10 (:REWRITE DEFAULT-MINUS))
     (42 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (42 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (41 29 (:REWRITE DEFAULT-LESS-THAN-1))
     (38 6
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (38 6 (:REWRITE MOD-CANCEL-*-CONST))
     (38 6
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (38 6
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (38 4 (:REWRITE POSP-PFIX-IDENTITY))
     (38 2 (:REWRITE |(* x (if a b c))|))
     (37 29 (:REWRITE SIMPLIFY-SUMS-<))
     (37 29 (:REWRITE DEFAULT-LESS-THAN-2))
     (32 4 (:LINEAR MOD-BOUNDS-2))
     (29 29 (:REWRITE THE-FLOOR-BELOW))
     (29 29 (:REWRITE THE-FLOOR-ABOVE))
     (29 29
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (29 29
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (29 29
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (29 29
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (29 29 (:REWRITE INTEGERP-<-CONSTANT))
     (29 29 (:REWRITE CONSTANT-<-INTEGERP))
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
     (29 29 (:REWRITE |(< (/ x) (/ y))|))
     (29 29 (:REWRITE |(< (- x) c)|))
     (29 29 (:REWRITE |(< (- x) (- y))|))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (24 24
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 6 (:REWRITE |(* y x)|))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21 (:REWRITE REDUCE-INTEGERP-+))
     (21 21 (:REWRITE INTEGERP-MINUS-X))
     (21 21 (:META META-INTEGERP-CORRECT))
     (20 16 (:REWRITE DEFAULT-MOD-2))
     (20 16 (:REWRITE DEFAULT-MOD-1))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< 0 (/ x))|))
     (11 11 (:REWRITE |(< 0 (* x y))|))
     (10 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE |(- (* c x))|))
     (6 6 (:REWRITE |(* 1 x)|))
     (6 6 (:REWRITE |(* 0 x)|))
     (6 2 (:REWRITE |(/ (if a b c))|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:TYPE-PRESCRIPTION POSP)))
(MOD-CTX-PMOD-REDUCTION
     (42 1 (:REWRITE CANCEL-MOD-+))
     (35 1 (:REWRITE MOD-X-Y-=-X . 4))
     (31 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (30 1 (:REWRITE MOD-X-Y-=-X . 3))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (24 1 (:REWRITE MOD-ZERO . 3))
     (18 1 (:REWRITE MOD-ZERO . 4))
     (16 1 (:REWRITE |(integerp (- x))|))
     (13 1 (:REWRITE DEFAULT-MOD-RATIO))
     (13 1 (:REWRITE |(* (- x) y)|))
     (12 3 (:REWRITE |(* y x)|))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (7 7 (:REWRITE DEFAULT-TIMES-2))
     (7 7 (:REWRITE DEFAULT-TIMES-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (5 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (5 1 (:REWRITE MOD-X-Y-=-X . 2))
     (5 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE MOD-CANCEL-*-CONST))
     (5 1 (:REWRITE DEFAULT-MINUS))
     (5 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (5 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (5 1
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (5 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE DEFAULT-DIVIDE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(- (* c x))|)))
(PMOD-CONGRUENCE
     (10966 26 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (6004 116
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5846 26 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (4781 4781
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4781 4781
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4781 4781
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (3695 739 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3459 739 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3211 94 (:REWRITE CANCEL-MOD-+))
     (2937 94 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (2923 739
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2923 739
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2884 94 (:REWRITE MOD-X-Y-=-X . 4))
     (2864 94 (:REWRITE MOD-X-Y-=-X . 3))
     (2834 94 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (1706 86 (:LINEAR MOD-BOUNDS-2))
     (1686 94 (:REWRITE MOD-ZERO . 3))
     (1126 1086 (:REWRITE DEFAULT-TIMES-2))
     (1122 1086 (:REWRITE DEFAULT-TIMES-1))
     (1105 94 (:REWRITE MOD-ZERO . 4))
     (1055 91 (:REWRITE |(* (- x) y)|))
     (986 43 (:LINEAR MOD-BOUNDS-3))
     (984 60 (:REWRITE |(integerp (- x))|))
     (871 871
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (871 871
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (828 116
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (739 739 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (739 739
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (739 739
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (739 739
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (739 739 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (572 94 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (572 94 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (556 94 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (556 94
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (548 94 (:REWRITE MOD-X-Y-=-X . 2))
     (534 100 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (483 455 (:REWRITE DEFAULT-DIVIDE))
     (481 481
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (473 433
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (473 433
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (460 436 (:REWRITE DEFAULT-LESS-THAN-1))
     (452 436 (:REWRITE DEFAULT-LESS-THAN-2))
     (450 450
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (446 94 (:REWRITE MOD-CANCEL-*-CONST))
     (440 440 (:REWRITE THE-FLOOR-BELOW))
     (440 440 (:REWRITE THE-FLOOR-ABOVE))
     (435 435
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (435 435
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (433 433
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (433 433 (:REWRITE INTEGERP-<-CONSTANT))
     (433 433 (:REWRITE CONSTANT-<-INTEGERP))
     (433 433
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (433 433
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (433 433
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (433 433
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (433 433 (:REWRITE |(< c (- x))|))
     (433 433
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (433 433
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (433 433
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (433 433
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (433 433 (:REWRITE |(< (/ x) (/ y))|))
     (433 433 (:REWRITE |(< (- x) c)|))
     (433 433 (:REWRITE |(< (- x) (- y))|))
     (414 94
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (414 94
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (414 94
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (385 204 (:REWRITE DEFAULT-PLUS-2))
     (366 106 (:REWRITE DEFAULT-MINUS))
     (300 4
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (258 258 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (255 204 (:REWRITE DEFAULT-PLUS-1))
     (226 210 (:REWRITE INTEGERP-MINUS-X))
     (209 209 (:META META-INTEGERP-CORRECT))
     (204 204 (:REWRITE |(< (* x y) 0)|))
     (203 203
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (203 203
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (203 203 (:REWRITE |(< (/ x) 0)|))
     (190 94
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (190 94
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (190 94
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (137 137
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (137 137
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (137 137 (:REWRITE |(< 0 (/ x))|))
     (137 137 (:REWRITE |(< 0 (* x y))|))
     (116 116
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (116 116
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (116 116
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (116 116 (:REWRITE |(equal c (/ x))|))
     (116 116 (:REWRITE |(equal c (- x))|))
     (116 116 (:REWRITE |(equal (/ x) c)|))
     (116 116 (:REWRITE |(equal (/ x) (/ y))|))
     (116 116 (:REWRITE |(equal (- x) c)|))
     (116 116 (:REWRITE |(equal (- x) (- y))|))
     (115 107 (:REWRITE DEFAULT-MOD-2))
     (95 95 (:REWRITE |(- (* c x))|))
     (94 94 (:REWRITE |(mod x (- y))| . 3))
     (94 94 (:REWRITE |(mod x (- y))| . 2))
     (94 94 (:REWRITE |(mod x (- y))| . 1))
     (94 94 (:REWRITE |(mod (- x) y)| . 3))
     (94 94 (:REWRITE |(mod (- x) y)| . 2))
     (94 94 (:REWRITE |(mod (- x) y)| . 1))
     (91 19 (:REWRITE RATIONALP-X))
     (71 71
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (69 69
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (66 4 (:REWRITE POSP-PFIX-IDENTITY))
     (64 24
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (54 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (52 4 (:REWRITE |(* x (if a b c))|))
     (48 7 (:REWRITE MOD-ZERO . 2))
     (40 40 (:REWRITE |(equal (+ (- c) x) y)|))
     (34 4 (:REWRITE |(* (if a b c) x)|))
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
     (24 3 (:REWRITE ACL2-NUMBERP-X))
     (23 23 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (19 19 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:META META-RATIONALP-CORRECT))
     (12 4 (:REWRITE |(/ (if a b c))|))
     (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(* 0 x)|))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE MOD-POSITIVE . 3))
     (3 3 (:REWRITE MOD-POSITIVE . 2))
     (3 3 (:REWRITE INTEGERP-MOD-2))
     (3 3 (:REWRITE INTEGERP-MOD-1))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|)))
(PMOD-NEGATION
     (518 518
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (518 518
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (518 518
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (460 116 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (460 116 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (444 116
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (444 116
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (296 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (249 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (234 7 (:REWRITE MOD-X-Y-=-X . 3))
     (233 7 (:REWRITE MOD-X-Y-=-X . 4))
     (180 7 (:REWRITE CANCEL-MOD-+))
     (177 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (155 9 (:REWRITE MOD-ZERO . 4))
     (123 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (116 116 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (116 116
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (116 116
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (116 116
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (116 116 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (102 9 (:REWRITE DEFAULT-MOD-RATIO))
     (93 32 (:REWRITE |(< (- x) c)|))
     (74 46 (:REWRITE DEFAULT-PLUS-2))
     (72 24 (:REWRITE DEFAULT-MINUS))
     (69 69 (:REWRITE DEFAULT-TIMES-2))
     (69 69 (:REWRITE DEFAULT-TIMES-1))
     (64 33 (:REWRITE |(< c (- x))|))
     (63 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (53 46 (:REWRITE DEFAULT-PLUS-1))
     (45 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (45 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (37 23 (:REWRITE |(equal (- x) c)|))
     (35 7 (:REWRITE MOD-X-Y-=-X . 2))
     (35 7
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (35 7 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (35 7
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (33 33 (:REWRITE THE-FLOOR-BELOW))
     (33 33 (:REWRITE THE-FLOOR-ABOVE))
     (33 33
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (33 33
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (33 33
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (33 33 (:REWRITE DEFAULT-LESS-THAN-2))
     (33 33 (:REWRITE DEFAULT-LESS-THAN-1))
     (33 33
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (33 33
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (33 33
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (33 33
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (33 33 (:REWRITE |(< (/ x) (/ y))|))
     (33 33 (:REWRITE |(< (- x) (- y))|))
     (31 31
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (31 7 (:REWRITE MOD-CANCEL-*-CONST))
     (30 30 (:REWRITE SIMPLIFY-SUMS-<))
     (30 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 30
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (30 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (30 30 (:REWRITE INTEGERP-<-CONSTANT))
     (30 30 (:REWRITE DEFAULT-DIVIDE))
     (30 30 (:REWRITE CONSTANT-<-INTEGERP))
     (30 6
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (30 6
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (23 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (23 23
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (23 23 (:REWRITE |(equal c (/ x))|))
     (23 23 (:REWRITE |(equal c (- x))|))
     (23 23 (:REWRITE |(equal (/ x) c)|))
     (23 23 (:REWRITE |(equal (/ x) (/ y))|))
     (23 23 (:REWRITE |(equal (- x) (- y))|))
     (22 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 22
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (20 4 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE |(< 0 (/ x))|))
     (10 10 (:REWRITE |(< 0 (* x y))|))
     (10 2 (:REWRITE MOD-ZERO . 2))
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (9 9 (:REWRITE DEFAULT-MOD-2))
     (9 9 (:REWRITE DEFAULT-MOD-1))
     (9 9 (:REWRITE |(- (* c x))|))
     (7 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (7 7
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (7 7 (:REWRITE |(mod x (- y))| . 3))
     (7 7 (:REWRITE |(mod x (- y))| . 2))
     (7 7 (:REWRITE |(mod x (- y))| . 1))
     (7 7 (:REWRITE |(mod (- x) y)| . 3))
     (7 7 (:REWRITE |(mod (- x) y)| . 2))
     (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
     (6 6
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (6 6
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (4 1 (:REWRITE |(+ x x)|))
     (2 2
        (:REWRITE |(equal (mod (+ x y) z) x)|)))
(PMOD-SUM (1984 1984
                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (1984 1984
                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (1984 1984
                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (1970 394 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
          (1970 394 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
          (1970 394
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
          (1970 394
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
          (541 13 (:REWRITE CANCEL-MOD-+))
          (394 394 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
          (394 394
               (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
          (394 394
               (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
          (394 394
               (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
          (394 394 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
          (389 13 (:REWRITE MOD-X-Y-=-X . 4))
          (389 13 (:REWRITE MOD-X-Y-=-X . 3))
          (378 13 (:REWRITE MOD-X-Y-=-X+Y . 2))
          (345 13 (:REWRITE MOD-X-Y-=-X-Y . 2))
          (305 17 (:REWRITE DEFAULT-PLUS-2))
          (305 17 (:REWRITE DEFAULT-PLUS-1))
          (270 13 (:REWRITE MOD-ZERO . 3))
          (224 14 (:REWRITE |(integerp (- x))|))
          (201 13 (:REWRITE MOD-ZERO . 4))
          (162 13 (:REWRITE DEFAULT-MOD-RATIO))
          (159 47 (:REWRITE SIMPLIFY-SUMS-<))
          (159 47
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
          (159 47 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
          (159 47 (:REWRITE DEFAULT-LESS-THAN-1))
          (140 14 (:REWRITE |(* (- x) y)|))
          (72 16 (:REWRITE DEFAULT-MINUS))
          (65 13 (:REWRITE MOD-X-Y-=-X-Y . 3))
          (65 13 (:REWRITE MOD-X-Y-=-X+Y . 3))
          (65 13 (:REWRITE MOD-X-Y-=-X . 2))
          (65 13
              (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
          (65 13
              (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
          (65 13 (:REWRITE |(mod (+ x (mod a b)) y)|))
          (65 13
              (:REWRITE |(mod (+ x (- (mod a b))) y)|))
          (65 13
              (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
          (62 62 (:REWRITE DEFAULT-TIMES-2))
          (62 62 (:REWRITE DEFAULT-TIMES-1))
          (58 6 (:REWRITE |(* y x)|))
          (50 2 (:REWRITE |(* x (+ y z))|))
          (47 47 (:REWRITE THE-FLOOR-BELOW))
          (47 47 (:REWRITE THE-FLOOR-ABOVE))
          (47 47
              (:REWRITE REMOVE-STRICT-INEQUALITIES))
          (47 47
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
          (47 47
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
          (47 47
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
          (47 47 (:REWRITE INTEGERP-<-CONSTANT))
          (47 47 (:REWRITE DEFAULT-LESS-THAN-2))
          (47 47 (:REWRITE CONSTANT-<-INTEGERP))
          (47 47
              (:REWRITE |(< c (/ x)) positive c --- present in goal|))
          (47 47
              (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
          (47 47
              (:REWRITE |(< c (/ x)) negative c --- present in goal|))
          (47 47
              (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
          (47 47 (:REWRITE |(< c (- x))|))
          (47 47
              (:REWRITE |(< (/ x) c) positive c --- present in goal|))
          (47 47
              (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
          (47 47
              (:REWRITE |(< (/ x) c) negative c --- present in goal|))
          (47 47
              (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
          (47 47 (:REWRITE |(< (/ x) (/ y))|))
          (47 47 (:REWRITE |(< (- x) c)|))
          (47 47 (:REWRITE |(< (- x) (- y))|))
          (42 42
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
          (38 38
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
          (38 38 (:REWRITE DEFAULT-DIVIDE))
          (36 36 (:REWRITE REMOVE-WEAK-INEQUALITIES))
          (28 28 (:REWRITE REDUCE-INTEGERP-+))
          (28 28 (:REWRITE INTEGERP-MINUS-X))
          (28 28 (:META META-INTEGERP-CORRECT))
          (25 13 (:REWRITE MOD-CANCEL-*-CONST))
          (22 22
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (22 22
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (22 22 (:REWRITE |(< (/ x) 0)|))
          (22 22 (:REWRITE |(< (* x y) 0)|))
          (14 14 (:REWRITE |(- (* c x))|))
          (13 13
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (13 13 (:REWRITE NORMALIZE-ADDENDS))
          (13 13
              (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
          (13 13 (:REWRITE DEFAULT-MOD-2))
          (13 13 (:REWRITE DEFAULT-MOD-1))
          (13 13 (:REWRITE |(mod x (- y))| . 3))
          (13 13 (:REWRITE |(mod x (- y))| . 2))
          (13 13 (:REWRITE |(mod x (- y))| . 1))
          (13 13
              (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
          (13 13 (:REWRITE |(mod (- x) y)| . 3))
          (13 13 (:REWRITE |(mod (- x) y)| . 2))
          (13 13 (:REWRITE |(mod (- x) y)| . 1))
          (13 13
              (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
          (12 12
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
          (12 12
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
          (12 12 (:REWRITE |(< 0 (/ x))|))
          (12 12 (:REWRITE |(< 0 (* x y))|))
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
              (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
          (11 11 (:REWRITE |(equal c (/ x))|))
          (11 11 (:REWRITE |(equal c (- x))|))
          (11 11 (:REWRITE |(equal (/ x) c)|))
          (11 11 (:REWRITE |(equal (/ x) (/ y))|))
          (11 11 (:REWRITE |(equal (- x) c)|))
          (11 11 (:REWRITE |(equal (- x) (- y))|))
          (5 5 (:REWRITE |(< (+ c/d x) y)|))
          (5 5 (:REWRITE |(< (+ (- c) x) y)|))
          (2 2 (:REWRITE FOLD-CONSTS-IN-+))
          (2 2 (:REWRITE |(+ c (+ d x))|))
          (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
          (1 1
             (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
          (1 1
             (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
          (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
          (1 1 (:REWRITE |(< y (+ (- c) x))|))
          (1 1 (:REWRITE |(< x (+ c/d y))|)))
(FORCE-PMOD-REWRITING
     (670 134 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (670 134 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (662 662
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (662 662
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (662 662
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (574 134
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (574 134
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (470 8 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (457 36
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (294 7 (:REWRITE CANCEL-MOD-+))
     (266 36
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (246 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (245 7 (:REWRITE MOD-X-Y-=-X . 4))
     (245 7 (:REWRITE MOD-X-Y-=-X . 3))
     (238 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (230 8 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (217 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (168 7 (:REWRITE MOD-ZERO . 3))
     (134 134 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (134 134
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (134 134
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (134 134
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (134 134 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (126 7 (:REWRITE MOD-ZERO . 4))
     (112 7 (:REWRITE |(integerp (- x))|))
     (91 7 (:REWRITE DEFAULT-MOD-RATIO))
     (91 7 (:REWRITE |(* (- x) y)|))
     (84 21 (:REWRITE |(* y x)|))
     (80 26 (:REWRITE NORMALIZE-ADDENDS))
     (70 14 (:REWRITE |(+ y x)|))
     (58 52 (:REWRITE DEFAULT-PLUS-2))
     (58 52 (:REWRITE DEFAULT-PLUS-1))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (49 49 (:REWRITE DEFAULT-TIMES-2))
     (49 49 (:REWRITE DEFAULT-TIMES-1))
     (42 14 (:REWRITE DEFAULT-MINUS))
     (36 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (36 36
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (36 36
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (36 36 (:REWRITE |(equal c (/ x))|))
     (36 36 (:REWRITE |(equal c (- x))|))
     (36 36 (:REWRITE |(equal (/ x) c)|))
     (36 36 (:REWRITE |(equal (/ x) (/ y))|))
     (36 36 (:REWRITE |(equal (- x) c)|))
     (36 36 (:REWRITE |(equal (- x) (- y))|))
     (35 35 (:REWRITE THE-FLOOR-BELOW))
     (35 35 (:REWRITE THE-FLOOR-ABOVE))
     (35 35 (:REWRITE SIMPLIFY-SUMS-<))
     (35 35
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (35 35
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (35 35
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (35 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (35 35 (:REWRITE INTEGERP-<-CONSTANT))
     (35 35 (:REWRITE DEFAULT-LESS-THAN-2))
     (35 35 (:REWRITE DEFAULT-LESS-THAN-1))
     (35 35 (:REWRITE CONSTANT-<-INTEGERP))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (35 35 (:REWRITE |(< c (- x))|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (35 35 (:REWRITE |(< (/ x) (/ y))|))
     (35 35 (:REWRITE |(< (- x) c)|))
     (35 35 (:REWRITE |(< (- x) (- y))|))
     (35 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (35 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (35 7 (:REWRITE MOD-X-Y-=-X . 2))
     (35 7
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (35 7 (:REWRITE MOD-CANCEL-*-CONST))
     (35 7
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (35 7 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (35 7
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (35 7
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (30 6 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:META META-INTEGERP-CORRECT))
     (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (21 21
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (21 21 (:REWRITE DEFAULT-DIVIDE))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< 0 (/ x))|))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:REWRITE |(< (* x y) 0)|))
     (12 12 (:DEFINITION FIX))
     (11 3 (:REWRITE ACL2-NUMBERP-X))
     (8 8
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (7 7
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (7 7 (:REWRITE DEFAULT-MOD-2))
     (7 7 (:REWRITE DEFAULT-MOD-1))
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
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (6 6 (:REWRITE |(+ x (- x))|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE |(+ 0 x)|))
     (4 1 (:REWRITE RATIONALP-X))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT)))
(MINIMAL-FRACTIONS-PAIR-P)
(SMALLEST-COEFFICIENT-PAIR-P)
(PFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-1)
(NFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-2)
(NFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-3)
(NFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-4)
(PFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-5)
(SMALLEST-COEFFICIENT-PAIR-WITNESS-STRENGTHEN)
(SMALLEST-COEFFICIENT-PAIR)
(SMALLEST-COEFFICIENT-PAIR-NECC)
(SMALLEST-COEFFICIENT-PAIR-EQUIV)
(QUANT::SMALLEST-COEFFICIENT-PAIR-CONGRUENT-PREDICATE)
(QUANT::SMALLEST-COEFFICIENT-PAIR-EQUIV)
(QUANT::BIG-BANG-CONGRUENCE)
(QUANT::SMALLEST-COEFFICIENT-PAIR-DEFINITION
     (1 1
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC)))
(QUANT::CONGRUENT-PREDICATE-WITNESS-CANARY
     (2 2
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
(SMALLEST-COEFFICIENT-PAIR-WITNESS-CONGRUENCE)
(SMALLEST-COEFFICIENT-PAIR-CONGRUENCE)
(SMALLEST-COEFFICIENT-PAIR-IMPLICATION)
(DELTA)
(SMALLEST-COEFFICIENT-PAIR-INVARIANT-1-HELPER
     (26123 16546 (:REWRITE DEFAULT-PLUS-2))
     (22334 16546 (:REWRITE DEFAULT-PLUS-1))
     (5682 5682
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5174 3731 (:REWRITE DEFAULT-LESS-THAN-1))
     (4915 3731 (:REWRITE DEFAULT-LESS-THAN-2))
     (3856 3127 (:REWRITE DEFAULT-MINUS))
     (3731 3731 (:REWRITE THE-FLOOR-BELOW))
     (3731 3731 (:REWRITE THE-FLOOR-ABOVE))
     (3564 3486 (:REWRITE |(< (- x) (- y))|))
     (3499 3496
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3499 3496
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3496 3496
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3486 3486
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3486 3486 (:REWRITE INTEGERP-<-CONSTANT))
     (3486 3486 (:REWRITE CONSTANT-<-INTEGERP))
     (3486 3486
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3486 3486
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3486 3486
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3486 3486
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3486 3486 (:REWRITE |(< c (- x))|))
     (3486 3486
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3486 3486
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3486 3486
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3486 3486
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3486 3486 (:REWRITE |(< (/ x) (/ y))|))
     (3486 3486 (:REWRITE |(< (- x) c)|))
     (3398 3348 (:REWRITE DEFAULT-TIMES-2))
     (3356 3348 (:REWRITE DEFAULT-TIMES-1))
     (2233 1794 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2213 2213 (:REWRITE |(+ c (+ d x))|))
     (1961 1961
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1066 1066 (:REWRITE |(< y (+ (- c) x))|))
     (1066 1066 (:REWRITE |(< x (+ c/d y))|))
     (1056 1056 (:REWRITE FOLD-CONSTS-IN-+))
     (1037 1037 (:REWRITE |(< (+ c/d x) y)|))
     (1037 1037 (:REWRITE |(< (+ (- c) x) y)|))
     (943 943 (:REWRITE REDUCE-INTEGERP-+))
     (943 943 (:REWRITE INTEGERP-MINUS-X))
     (943 943 (:META META-INTEGERP-CORRECT))
     (601 601 (:REWRITE |(< (/ x) 0)|))
     (601 601 (:REWRITE |(< (* x y) 0)|))
     (598 598
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (598 598
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (468 306
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (342 342 (:REWRITE |(< 0 (* x y))|))
     (332 332 (:REWRITE |(< 0 (/ x))|))
     (310 308 (:REWRITE |(equal (/ x) (/ y))|))
     (308 308
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (308 308
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (308 308 (:REWRITE |(equal c (/ x))|))
     (308 308 (:REWRITE |(equal (- x) (- y))|))
     (306 306
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (306 306 (:REWRITE |(equal c (- x))|))
     (306 306 (:REWRITE |(equal (- x) c)|))
     (286 253 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (236 236
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (236 236
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (203 203
          (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (199 199
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (68 68 (:REWRITE |(equal (+ (- c) x) y)|))
     (18 10
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (14 10
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (14 10
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (12 12 (:REWRITE |(* (- x) y)|))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 2 (:REWRITE |(equal x (/ y))|))
     (4 2 (:REWRITE DEFAULT-DIVIDE))
     (4 2 (:REWRITE |(not (equal x (/ y)))|)))
(SMALLEST-COEFFICIENT-PAIR-INVARIANT-2-HELPER
     (40558 28466 (:REWRITE DEFAULT-PLUS-2))
     (37499 28466 (:REWRITE DEFAULT-PLUS-1))
     (8761 8761
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8429 6090 (:REWRITE DEFAULT-LESS-THAN-1))
     (7521 6090 (:REWRITE DEFAULT-LESS-THAN-2))
     (7105 5413 (:REWRITE DEFAULT-MINUS))
     (6090 6090 (:REWRITE THE-FLOOR-BELOW))
     (6090 6090 (:REWRITE THE-FLOOR-ABOVE))
     (5770 5679 (:REWRITE |(< (- x) (- y))|))
     (5725 5714
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5725 5714
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5714 5714
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5679 5679
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5679 5679
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5679 5679
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5679 5679
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5679 5679
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5679 5679
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5679 5679
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5679 5679
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5679 5679 (:REWRITE |(< (/ x) (/ y))|))
     (5676 5676 (:REWRITE INTEGERP-<-CONSTANT))
     (5676 5676 (:REWRITE CONSTANT-<-INTEGERP))
     (5676 5676 (:REWRITE |(< (- x) c)|))
     (4716 4674 (:REWRITE DEFAULT-TIMES-2))
     (4674 4674 (:REWRITE DEFAULT-TIMES-1))
     (4071 3355 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3292 3292 (:REWRITE |(+ c (+ d x))|))
     (2779 2779
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2172 2172 (:REWRITE |(< y (+ (- c) x))|))
     (2172 2172 (:REWRITE |(< x (+ c/d y))|))
     (1776 1776 (:REWRITE |(< (+ c/d x) y)|))
     (1776 1776 (:REWRITE |(< (+ (- c) x) y)|))
     (1673 1673 (:REWRITE FOLD-CONSTS-IN-+))
     (1301 1301 (:REWRITE REDUCE-INTEGERP-+))
     (1301 1301 (:REWRITE INTEGERP-MINUS-X))
     (1301 1301 (:META META-INTEGERP-CORRECT))
     (908 636
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (893 893 (:REWRITE |(< (/ x) 0)|))
     (893 893 (:REWRITE |(< (* x y) 0)|))
     (889 889
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (889 889
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (636 636
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (636 636
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (636 636
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (636 636 (:REWRITE |(equal c (/ x))|))
     (636 636 (:REWRITE |(equal c (- x))|))
     (636 636 (:REWRITE |(equal (/ x) c)|))
     (636 636 (:REWRITE |(equal (/ x) (/ y))|))
     (636 636 (:REWRITE |(equal (- x) c)|))
     (636 636 (:REWRITE |(equal (- x) (- y))|))
     (603 526 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (585 585 (:REWRITE |(< 0 (* x y))|))
     (550 550 (:REWRITE |(< 0 (/ x))|))
     (450 450
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (450 450
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (413 413
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (283 283
          (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (142 142 (:REWRITE |(equal (+ (- c) x) y)|))
     (35 35
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (35 35
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (35 35
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (22 22 (:TYPE-PRESCRIPTION ABS))
     (21 21 (:REWRITE |(* (- x) y)|)))
(SMALLEST-COEFFICIENT-PAIR-INVARIANT-1
     (42 28 (:REWRITE DEFAULT-PLUS-2))
     (42 28 (:REWRITE DEFAULT-PLUS-1))
     (33 1 (:DEFINITION POSP))
     (30 15 (:REWRITE PMOD-CONGRUENCE))
     (29 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (28 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (23 17 (:REWRITE SIMPLIFY-SUMS-<))
     (22 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (20 20
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (20 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE MOD-*-CONGRUENCE))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 8 (:REWRITE DEFAULT-MINUS))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE DEFAULT-TIMES-1))
     (5 5
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(SMALLEST-COEFFICIENT-PAIR-INVARIANT-2
     (42 28 (:REWRITE DEFAULT-PLUS-2))
     (42 28 (:REWRITE DEFAULT-PLUS-1))
     (33 1 (:DEFINITION POSP))
     (32 20
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 20
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (30 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (30 15 (:REWRITE PMOD-CONGRUENCE))
     (26 18 (:REWRITE SIMPLIFY-SUMS-<))
     (22 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (20 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE MOD-*-CONGRUENCE))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 8 (:REWRITE DEFAULT-MINUS))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE DEFAULT-TIMES-1))
     (5 5
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(SMALLEST-COEFFICIENT-PAIR-IMPLIES-MINIMAL-FRACTIONS-PAIR-P
     (122 62 (:REWRITE DEFAULT-+-2))
     (91 62 (:REWRITE DEFAULT-+-1))
     (79 49 (:REWRITE PMOD-CONGRUENCE))
     (72 54 (:REWRITE DEFAULT-<-2))
     (63 54 (:REWRITE DEFAULT-<-1))
     (50 37 (:REWRITE DEFAULT-UNARY-MINUS))
     (32 32 (:REWRITE DEFAULT-*-2))
     (32 32 (:REWRITE DEFAULT-*-1))
     (30 30 (:REWRITE MOD-*-CONGRUENCE))
     (18 18 (:REWRITE FOLD-CONSTS-IN-+))
     (16 8 (:REWRITE FORCE-PMOD-REWRITING))
     (7 7
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC)))
(STEP-MINIMAL-FRACTIONS-PAIR)
(NATP-NEGP-NATP-NATP-IMPLIES-NATP-NEGP-NATP-NATP-STEP-MINIMAL-FRACTIONS-PAIR
     (56 56 (:REWRITE DEFAULT-<-2))
     (56 56 (:REWRITE DEFAULT-<-1))
     (36 36 (:REWRITE DEFAULT-+-2))
     (36 36 (:REWRITE DEFAULT-+-1))
     (13 13 (:REWRITE DEFAULT-UNARY-MINUS)))
(STEP-MINIMAL-FRACTIONS-PAIR)
(SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR
     (106 58 (:REWRITE DEFAULT-+-2))
     (88 58 (:REWRITE DEFAULT-+-1))
     (84 42 (:REWRITE PMOD-CONGRUENCE))
     (43 34 (:REWRITE DEFAULT-UNARY-MINUS))
     (42 42 (:REWRITE MOD-*-CONGRUENCE))
     (38 38 (:REWRITE DEFAULT-*-2))
     (38 38 (:REWRITE DEFAULT-*-1))
     (30 21 (:REWRITE DEFAULT-<-1))
     (25 21 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE FOLD-CONSTS-IN-+))
     (5 5
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC)))
(SMALLEST-COEFFICIENT-PAIR-P-INIT-HELPER
     (13 10 (:REWRITE PMOD-CONGRUENCE))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (6 4 (:REWRITE DEFAULT-+-2))
     (6 4 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 2 (:REWRITE FORCE-PMOD-REWRITING))
     (3 3 (:REWRITE MOD-*-CONGRUENCE))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(SMALLEST-COEFFICIENT-PAIR-INIT
     (10 2 (:REWRITE POSP-PFIX-IDENTITY))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC)))
(MAGNITUDE-INVARIANT (24 24 (:REWRITE DEFAULT-*-2))
                     (24 24 (:REWRITE DEFAULT-*-1))
                     (22 17 (:REWRITE DEFAULT-+-1))
                     (17 17 (:REWRITE DEFAULT-+-2))
                     (15 15 (:REWRITE DEFAULT-<-2))
                     (15 15 (:REWRITE DEFAULT-<-1))
                     (5 5
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(LT-SQRT)
(NUM-EQUAL)
(PROD)
(MAGNITUDE-INVARIANT-HELPER
     (33 31 (:REWRITE DEFAULT-PLUS-1))
     (31 31 (:REWRITE DEFAULT-PLUS-2))
     (24 24 (:REWRITE DEFAULT-TIMES-2))
     (24 24 (:REWRITE DEFAULT-TIMES-1))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (15 15 (:REWRITE THE-FLOOR-BELOW))
     (15 15 (:REWRITE THE-FLOOR-ABOVE))
     (15 15 (:REWRITE SIMPLIFY-SUMS-<))
     (15 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (15 15
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (15 15 (:REWRITE INTEGERP-<-CONSTANT))
     (15 15 (:REWRITE DEFAULT-LESS-THAN-2))
     (15 15 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15 (:REWRITE CONSTANT-<-INTEGERP))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< c (- x))|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 15 (:REWRITE |(< (- x) c)|))
     (15 15 (:REWRITE |(< (- x) (- y))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:REWRITE DEFAULT-MINUS))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (12 12 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE |(- (* c x))|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(NEGATIVE-PRODUCT (56 8 (:REWRITE ACL2-NUMBERP-X))
                  (24 6 (:REWRITE RATIONALP-X))
                  (6 6 (:REWRITE REDUCE-RATIONALP-+))
                  (6 6 (:REWRITE REDUCE-RATIONALP-*))
                  (6 6 (:REWRITE REDUCE-INTEGERP-+))
                  (6 6 (:REWRITE RATIONALP-MINUS-X))
                  (6 6 (:REWRITE INTEGERP-MINUS-X))
                  (6 6 (:META META-RATIONALP-CORRECT))
                  (6 6 (:META META-INTEGERP-CORRECT))
                  (2 2
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (2 2 (:REWRITE |(- (* c x))|)))
(POSP-PROD)
(LTE-SQUARE-LTE (11 11
                    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
                (9 9 (:REWRITE |arith (* c (* d x))|))
                (4 4 (:REWRITE |arith (- (* c x))|))
                (4 4 (:REWRITE |arith (* (- x) y)|)))
(LTE-PROPERTY (24 24
                  (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
              (22 22 (:REWRITE |arith (* c (* d x))|))
              (9 9 (:REWRITE |arith (- (* c x))|))
              (9 9 (:REWRITE |arith (* (- x) y)|)))
(PRODUCT-OF-NLT-SQRT
 (390
   390
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (390
  390
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (390 390
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (390
     390
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (390 390
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (390 390
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (218 58 (:REWRITE DEFAULT-TIMES-2))
 (203 203
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (203 203
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (184 18 (:REWRITE SIMPLIFY-SUMS-<))
 (184 18
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (184 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (148 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (117 58 (:REWRITE DEFAULT-TIMES-1))
 (54 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (18 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 18
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 18
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE |(* c (* d x))|)))
(NOT-NUM-EQUAL-1)
(NOT-NUM-EQUAL-2)
(NEGATIVE-LT-SQRT
 (54 6 (:REWRITE ACL2-NUMBERP-X))
 (53 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (53 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (29 5 (:REWRITE SIMPLIFY-SUMS-<))
 (27 3 (:REWRITE DEFAULT-MINUS))
 (24 6 (:REWRITE RATIONALP-X))
 (17 17
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
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
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 6 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|)))
(ONE-FRACTION-LT-SQRT-HELPER-1
     (28 21 (:REWRITE SIMPLIFY-SUMS-<))
     (28 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (28 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 21 (:REWRITE DEFAULT-LESS-THAN-1))
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (21 16 (:REWRITE DEFAULT-PLUS-2))
     (21 16 (:REWRITE DEFAULT-PLUS-1))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:REWRITE DEFAULT-MINUS))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
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
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:TYPE-PRESCRIPTION NATP)))
(ONE-FRACTION-LT-SQRT-HELPER-2)
(ONE-FRACTION-LT-SQRT-NEQ)
(EQUAL-P--N
 (95 33 (:REWRITE DEFAULT-TIMES-2))
 (39 33 (:REWRITE DEFAULT-TIMES-1))
 (27 9 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE |(< 0 (* x y))|))
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
 (3 3 (:REWRITE |(* (/ c) (expt d n))|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE NEGATIVE-LT-SQRT))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LT-SQRT-NEGATIVE
 (210 6 (:REWRITE NEGATIVE-LT-SQRT))
 (162 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (128 16 (:REWRITE ACL2-NUMBERP-X))
 (106 16 (:REWRITE |(< (- x) c)|))
 (78 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (65 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (62 62
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (62
   62
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (62
  62
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (56 14 (:REWRITE RATIONALP-X))
 (52 13 (:REWRITE SIMPLIFY-SUMS-<))
 (29 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (29 3
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (29 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (23 23 (:REWRITE THE-FLOOR-BELOW))
 (23 23 (:REWRITE THE-FLOOR-ABOVE))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE REDUCE-INTEGERP-+))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:REWRITE INTEGERP-MINUS-X))
 (14 14 (:META META-RATIONALP-CORRECT))
 (14 14 (:META META-INTEGERP-CORRECT))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13 (:REWRITE CONSTANT-<-INTEGERP))
 (13 10 (:REWRITE DEFAULT-TIMES-1))
 (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|)))
(ONE-FRACTION-LT-SQRT-ALT
 (266 175 (:REWRITE DEFAULT-PLUS-1))
 (234 175 (:REWRITE DEFAULT-PLUS-2))
 (204 162 (:REWRITE DEFAULT-TIMES-2))
 (186 186
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (186 186
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (186 186
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (171 162 (:REWRITE DEFAULT-TIMES-1))
 (83 83
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (76 76 (:REWRITE DEFAULT-MINUS))
 (46 46 (:REWRITE |(- (* c x))|))
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
 (29 29 (:REWRITE |(equal (+ (- c) x) y)|))
 (27 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (20 20
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (20 20 (:REWRITE DEFAULT-EXPT-2))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (19 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (19 19 (:REWRITE CONSTANT-<-INTEGERP))
 (19 19 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(expt (- c) n)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(* (/ c) (expt d n))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(LT-SQRT-0 (36 4 (:REWRITE ACL2-NUMBERP-X))
           (16 4 (:REWRITE RATIONALP-X))
           (4 4 (:REWRITE THE-FLOOR-BELOW))
           (4 4 (:REWRITE THE-FLOOR-ABOVE))
           (4 4 (:REWRITE REDUCE-RATIONALP-+))
           (4 4 (:REWRITE REDUCE-RATIONALP-*))
           (4 4 (:REWRITE REDUCE-INTEGERP-+))
           (4 4 (:REWRITE RATIONALP-MINUS-X))
           (4 4 (:REWRITE INTEGERP-MINUS-X))
           (4 4 (:META META-RATIONALP-CORRECT))
           (4 4 (:META META-INTEGERP-CORRECT))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
           (2 2 (:REWRITE SIMPLIFY-SUMS-<))
           (2 2
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (2 2
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (2 2
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (2 2 (:REWRITE INTEGERP-<-CONSTANT))
           (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
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
           (2 2 (:REWRITE |(< 0 (/ x))|))
           (2 2 (:REWRITE |(< 0 (* x y))|))
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
(ONE-FRACTION-LT-SQRT-NAT
 (125
   125
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (125 125
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (125 125
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (125 125
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (120 82 (:REWRITE DEFAULT-PLUS-1))
 (115 82 (:REWRITE DEFAULT-PLUS-2))
 (93 88 (:REWRITE DEFAULT-TIMES-1))
 (88 88 (:REWRITE DEFAULT-TIMES-2))
 (61 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (34 34 (:REWRITE DEFAULT-MINUS))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (33 33 (:REWRITE DEFAULT-LESS-THAN-2))
 (33 33 (:REWRITE DEFAULT-LESS-THAN-1))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (33 33
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (33 33 (:REWRITE |(< (/ x) (/ y))|))
 (33 33 (:REWRITE |(< (- x) (- y))|))
 (32 32
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (32 32
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (29 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (29 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (29 29
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (28 28 (:REWRITE SIMPLIFY-SUMS-<))
 (27 27 (:REWRITE |(- (* c x))|))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (12 12 (:REWRITE |(equal c (/ x))|))
 (12 12 (:REWRITE |(equal (/ x) c)|))
 (12 12 (:REWRITE |(equal (/ x) (/ y))|))
 (12 12 (:REWRITE |(equal (- x) (- y))|))
 (11 11
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11 11 (:REWRITE |(equal (- x) c)|))
 (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(ONE-FRACTION-LT-SQRT)
(MINIMAL-FRACTIONS-PAIR)
(MINIMAL-FRACTIONS-PAIR-NECC)
(SMALLEST-COEFFICIENT-PAIR-IMPLIES-MINIMAL-FRACTIONS-PAIR
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (5 1 (:REWRITE POSP-PFIX-IDENTITY))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 1 (:REWRITE PMOD-CONGRUENCE))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (1 1 (:REWRITE MOD-*-CONGRUENCE))
     (1 1
        (:REWRITE MINIMAL-FRACTIONS-PAIR-NECC)))
(MINIMAL-FRACTIONS-PAIR-LISTP)
(FRACTIONS-LISTP)
(MINIMAL-FRACTIONS-LIST-REC (30 23 (:REWRITE DEFAULT-+-1))
                            (29 25 (:REWRITE DEFAULT-<-1))
                            (29 23 (:REWRITE DEFAULT-+-2))
                            (25 25 (:REWRITE DEFAULT-<-2))
                            (13 12 (:REWRITE DEFAULT-UNARY-MINUS))
                            (8 8
                               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                            (3 3 (:REWRITE FOLD-CONSTS-IN-+)))
(NATP-NEGP-NATP-NATP-IMPLIES-FRACTIONS-LISTP-MINIMAL-FRACTIONS-LIST-REC
     (172 167 (:REWRITE DEFAULT-CDR))
     (137 132 (:REWRITE DEFAULT-<-1))
     (132 132 (:REWRITE DEFAULT-<-2))
     (101 97 (:REWRITE DEFAULT-+-2))
     (101 97 (:REWRITE DEFAULT-+-1))
     (54 49 (:REWRITE DEFAULT-CAR))
     (32 4 (:REWRITE COMMUTATIVITY-OF-+))
     (27 26 (:REWRITE DEFAULT-UNARY-MINUS))
     (24 4 (:REWRITE COMMUTATIVITY-2-OF-+))
     (14 14
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (5 1
        (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (2 2 (:TYPE-PRESCRIPTION NATP)))
(MINIMAL-FRACTIONS-LIST-REC (33 33 (:REWRITE DEFAULT-<-2))
                            (33 33 (:REWRITE DEFAULT-<-1))
                            (8 8 (:REWRITE DEFAULT-+-2))
                            (8 8 (:REWRITE DEFAULT-+-1))
                            (3 3 (:REWRITE DEFAULT-UNARY-MINUS)))
(MINIMAL-FRACTIONS-PAIR-LISTP-MINIMAL-FRACTIONS-LIST-REC
     (160 152 (:REWRITE DEFAULT-CDR))
     (117 101 (:REWRITE DEFAULT-*-2))
     (113 101 (:REWRITE DEFAULT-*-1))
     (89 83 (:REWRITE DEFAULT-<-2))
     (84 83 (:REWRITE DEFAULT-<-1))
     (77 43 (:REWRITE PMOD-CONGRUENCE))
     (70 7 (:DEFINITION MINIMAL-FRACTIONS-PAIR))
     (52 44 (:REWRITE DEFAULT-CAR))
     (42 14 (:DEFINITION POSP))
     (35 7 (:REWRITE POSP-PFIX-IDENTITY))
     (34 34 (:REWRITE MOD-*-CONGRUENCE))
     (28 28
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (28 7 (:DEFINITION PFIX))
     (7 7 (:TYPE-PRESCRIPTION POSP))
     (7 7
        (:TYPE-PRESCRIPTION MINIMAL-FRACTIONS-PAIR-P))
     (7 7
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-NECC))
     (7 7
        (:REWRITE MINIMAL-FRACTIONS-PAIR-NECC)))
(MINIMAL-FRACTIONS-LIST)
(INTEGERP-POSP-IMPLIES-FRACTIONS-LISTP-MINIMAL-FRACTIONS-LIST
     (39 1 (:DEFINITION FRACTIONS-LISTP))
     (18 2
         (:DEFINITION MINIMAL-FRACTIONS-LIST-REC))
     (17 17 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1))
     (9 3 (:DEFINITION NATP))
     (6 6 (:REWRITE PMOD-CONGRUENCE))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (4 2 (:REWRITE FORCE-PMOD-REWRITING))
     (2 2
        (:TYPE-PRESCRIPTION MINIMAL-FRACTIONS-LIST-REC))
     (2 2 (:REWRITE NATP-NFIX))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:DEFINITION IFIX)))
(MINIMAL-FRACTIONS-LIST (4 2 (:REWRITE FORCE-PMOD-REWRITING))
                        (3 3 (:REWRITE PMOD-CONGRUENCE))
                        (2 2 (:REWRITE DEFAULT-<-2))
                        (2 2 (:REWRITE DEFAULT-<-1))
                        (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(NMOD-ZERO (7 3 (:REWRITE POSP-PFIX-IDENTITY))
           (4 4 (:REWRITE DEFAULT-<-2))
           (4 4 (:REWRITE DEFAULT-<-1))
           (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
           (1 1 (:TYPE-PRESCRIPTION POSP))
           (1 1 (:REWRITE DEFAULT-+-2))
           (1 1 (:REWRITE DEFAULT-+-1)))
(TIMEZ-ZERO)
(MINIMAL-FRACTIONS-PAIR-LISTP-MINIMAL-FRACTIONS-LIST
     (18 2
         (:DEFINITION MINIMAL-FRACTIONS-LIST-REC))
     (17 17 (:REWRITE DEFAULT-CDR))
     (13 13 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-<-1))
     (10 10 (:REWRITE PMOD-CONGRUENCE))
     (10 1 (:DEFINITION MINIMAL-FRACTIONS-PAIR))
     (7 1
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-IMPLIES-MINIMAL-FRACTIONS-PAIR))
     (6 2 (:DEFINITION POSP))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (4 1 (:DEFINITION PFIX))
     (3 3
        (:TYPE-PRESCRIPTION MINIMAL-FRACTIONS-LIST-REC))
     (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE NATP-NFIX))
     (2 2 (:DEFINITION IFIX))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1
        (:TYPE-PRESCRIPTION MINIMAL-FRACTIONS-PAIR-P))
     (1 1
        (:REWRITE MINIMAL-FRACTIONS-PAIR-NECC))
     (1 1 (:REWRITE DEFAULT-*-2))
     (1 1 (:REWRITE DEFAULT-*-1)))
(PRINT-MINIMAL-FRACTIONS-PAIR-LIST (114 114 (:REWRITE DEFAULT-CDR))
                                   (20 20 (:REWRITE DEFAULT-CAR))
                                   (12 12 (:REWRITE DEFAULT-<-2))
                                   (12 12 (:REWRITE DEFAULT-<-1)))
(PRINT-ALL-MINIMAL-FRACTIONS)
(PRINT-ALL-MINIMAL-FRACTIONS)
(MINIMUM-FRACTION-REC (30 23 (:REWRITE DEFAULT-+-1))
                      (29 23 (:REWRITE DEFAULT-+-2))
                      (24 24
                          (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
                      (21 21 (:REWRITE DEFAULT-<-2))
                      (21 21 (:REWRITE DEFAULT-<-1))
                      (15 5 (:DEFINITION NATP))
                      (13 13 (:REWRITE DEFAULT-UNARY-MINUS))
                      (12 12
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(NATP-NEGP-NATP-NATP-POSP-IMPLIES-INTEGERP-NATP-MINIMUM-FRACTION-REC
     (1689 1685 (:REWRITE DEFAULT-<-2))
     (1687 1685 (:REWRITE DEFAULT-<-1))
     (497 497 (:REWRITE DEFAULT-*-2))
     (497 497 (:REWRITE DEFAULT-*-1))
     (431 431 (:REWRITE DEFAULT-UNARY-MINUS))
     (322 322
          (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(MINIMUM-FRACTION-REC
     (29 29 (:REWRITE DEFAULT-<-2))
     (29 29 (:REWRITE DEFAULT-<-1))
     (25 25 (:REWRITE DEFAULT-*-2))
     (25 25 (:REWRITE DEFAULT-*-1))
     (2 2
        (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(LT-SQRT-MINIMUM-FRACTION-REC
     (888 884 (:REWRITE DEFAULT-<-2))
     (884 884 (:REWRITE DEFAULT-<-1))
     (429 418 (:REWRITE DEFAULT-*-2))
     (429 418 (:REWRITE DEFAULT-*-1))
     (113 113 (:REWRITE DEFAULT-UNARY-MINUS))
     (109 109
          (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (93 89 (:REWRITE DEFAULT-+-2))
     (93 89 (:REWRITE DEFAULT-+-1))
     (22 22
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(LT-SQRT-1 (2 2 (:REWRITE DEFAULT-<-2))
           (2 2 (:REWRITE DEFAULT-<-1)))
(MINIMUM-FRACTION)
(INTEGERP-POSP-IMPLIES-INTEGERP-NATP-MINIMUM-FRACTION
     (175 5 (:DEFINITION MINIMUM-FRACTION-REC))
     (40 40
         (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
     (30 25 (:REWRITE DEFAULT-<-2))
     (25 25 (:REWRITE DEFAULT-<-1))
     (20 20 (:REWRITE DEFAULT-*-2))
     (20 20 (:REWRITE DEFAULT-*-1))
     (13 13 (:REWRITE PMOD-CONGRUENCE))
     (10 10
         (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (10 10 (:REWRITE LT-SQRT-NEGATIVE))
     (10 5 (:REWRITE NATP-NFIX))
     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (5 5 (:DEFINITION IFIX))
     (3 1 (:DEFINITION NATP)))
(MINIMUM-FRACTION (5 5 (:REWRITE DEFAULT-<-2))
                  (5 5 (:REWRITE DEFAULT-<-1))
                  (1 1 (:REWRITE PMOD-CONGRUENCE))
                  (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(LT-SQRT-MINIMUM-FRACTION
     (414 8 (:DEFINITION MINIMUM-FRACTION-REC))
     (80 72 (:REWRITE DEFAULT-<-2))
     (72 72 (:REWRITE DEFAULT-<-1))
     (72 24 (:DEFINITION MAX))
     (40 36 (:REWRITE DEFAULT-*-2))
     (40 36 (:REWRITE DEFAULT-*-1))
     (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
     (16 16
         (:REWRITE SMALLEST-COEFFICIENT-PAIR-STEP-MINIMAL-FRACTIONS-PAIR))
     (16 16 (:REWRITE LT-SQRT-NEGATIVE))
     (16 8 (:REWRITE NATP-NFIX))
     (12 12 (:REWRITE PMOD-CONGRUENCE))
     (8 8 (:DEFINITION IFIX))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(MINIMUM-FRACTION-LISTP)
(MINIMUM-FRACTION-LIST-REC (21 7 (:DEFINITION NATP))
                           (20 20 (:REWRITE DEFAULT-<-2))
                           (20 20 (:REWRITE DEFAULT-<-1))
                           (14 14 (:REWRITE DEFAULT-+-2))
                           (14 14 (:REWRITE DEFAULT-+-1))
                           (7 7 (:TYPE-PRESCRIPTION NATP))
                           (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                           (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(NATP-POSP-IMPLIES-MINIMUM-FRACTION-LISTP-MINIMUM-FRACTION-LIST-REC
     (31 30 (:REWRITE DEFAULT-CDR))
     (26 26 (:REWRITE DEFAULT-<-2))
     (26 26 (:REWRITE DEFAULT-<-1))
     (19 18 (:REWRITE DEFAULT-CAR))
     (9 9 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-+-1))
     (9 3 (:REWRITE FOLD-CONSTS-IN-+)))
(MINIMUM-FRACTION-LIST-REC)
(MINIMUM-FRACTION-LIST)
(POSP-IMPLIES-MINIMUM-FRACTION-LISTP-MINIMUM-FRACTION-LIST)
(MINIMUM-FRACTION-LIST)
(PRINT-MINIMUM-FRACTION-LIST (27 27 (:REWRITE DEFAULT-CDR))
                             (12 12 (:REWRITE DEFAULT-CAR))
                             (4 4 (:REWRITE DEFAULT-<-2))
                             (4 4 (:REWRITE DEFAULT-<-1))
                             (1 1 (:REWRITE DEFAULT-+-2))
                             (1 1 (:REWRITE DEFAULT-+-1)))
(PRINT-ALL-MINIMUM-FRACTIONS)
