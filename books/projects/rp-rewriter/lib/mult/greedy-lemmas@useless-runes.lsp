(RP::ALL-SUMS-IS-SUM)
(RP::M2-NEW-IS-M2)
(RP::F2-NEW-IS-F2)
(RP::D2-NEW-IS-D2)
(RP::SUM-OF-SINGLE-ELEMENT (5 5 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::TYPE-FIX-OF-FUNCTIONS
     (1123 1123
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1123 1123
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1123 1123
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (306 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (185 37
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (185 37
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (72 6 (:REWRITE DEFAULT-MOD-RATIO))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (50 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (44 11 (:REWRITE |(* y x)|))
     (40 40 (:REWRITE DEFAULT-TIMES-2))
     (40 40 (:REWRITE DEFAULT-TIMES-1))
     (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (37 37
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (37 37
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (28 4 (:REWRITE |(* (if a b c) x)|))
     (24 24
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (23 1 (:LINEAR MOD-BOUNDS-3))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20 (:META META-INTEGERP-CORRECT))
     (19 19 (:REWRITE DEFAULT-PLUS-2))
     (19 19 (:REWRITE DEFAULT-PLUS-1))
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE DEFAULT-MINUS))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (4 4 (:REWRITE |(mod x 2)| . 2))
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
     (2 2 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RP::FUNCTIONS-OF-TYPE-FIX (958 958
                                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                           (958 958
                                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                           (958 958
                                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                           (234 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                           (234 26
                                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                           (234 26
                                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                           (234 26
                                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                           (234 26
                                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                           (150 30 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                           (150 30 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                           (150 30
                                (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                           (150 30
                                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                           (130 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                           (130 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                           (130 26
                                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                           (30 30 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                           (30 30
                               (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                           (30 30 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                           (30 30
                               (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                           (30 30 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::F2-OF-REPEATED-TERMS-1
     (250 8 (:REWRITE DEFAULT-FLOOR-RATIO))
     (140 92 (:REWRITE DEFAULT-TIMES-2))
     (140 11 (:REWRITE |(* y x)|))
     (136 6 (:REWRITE |(* (if a b c) x)|))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (111 60 (:REWRITE DEFAULT-PLUS-2))
     (92 92 (:REWRITE DEFAULT-TIMES-1))
     (79 60 (:REWRITE DEFAULT-PLUS-1))
     (52 1 (:REWRITE |(floor (+ x r) i)|))
     (49 49
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (45 2
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (42 3 (:REWRITE |(* (* x y) z)|))
     (26 26 (:REWRITE INTEGERP-MINUS-X))
     (25 25
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (25 25 (:META META-INTEGERP-CORRECT))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE DEFAULT-FLOOR-1))
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
     (5 5 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 1 (:REWRITE O-INFP->NEQ-0))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:TYPE-PRESCRIPTION ABS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
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
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RP::F2-OF-REPEATED-TERMS-2 (37 2 (:REWRITE DEFAULT-FLOOR-RATIO))
                            (32 16 (:REWRITE DEFAULT-TIMES-2))
                            (28 2 (:REWRITE |(* (* x y) z)|))
                            (17 1 (:REWRITE |(* (if a b c) x)|))
                            (16 16 (:REWRITE DEFAULT-TIMES-1))
                            (8 2 (:REWRITE |(* y x)|))
                            (6 5 (:REWRITE DEFAULT-PLUS-1))
                            (5 5
                               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                            (5 5 (:REWRITE DEFAULT-PLUS-2))
                            (4 4 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
                            (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                            (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                            (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                            (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                            (3 3 (:REWRITE REDUCE-INTEGERP-+))
                            (3 3 (:REWRITE INTEGERP-MINUS-X))
                            (3 3
                               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                            (3 3 (:META META-INTEGERP-CORRECT))
                            (2 2 (:REWRITE DEFAULT-FLOOR-2))
                            (2 2 (:REWRITE DEFAULT-FLOOR-1))
                            (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                            (1 1 (:REWRITE |(floor x 2)| . 2)))
(RP::F2-OF-MINUS-LEMMA1
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (626 16 (:REWRITE DEFAULT-FLOOR-RATIO))
     (314 10 (:REWRITE |(* (if a b c) x)|))
     (306 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (187 75 (:REWRITE DEFAULT-PLUS-2))
     (181 75 (:REWRITE DEFAULT-PLUS-1))
     (176 176 (:REWRITE DEFAULT-TIMES-2))
     (176 176 (:REWRITE DEFAULT-TIMES-1))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (166 166
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (166 166
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (166 166
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (130 34 (:REWRITE DEFAULT-MINUS))
     (120 30 (:REWRITE |(* (- x) y)|))
     (112 112
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (104 24 (:REWRITE REDUCE-INTEGERP-+))
     (62 2 (:REWRITE |(floor (+ x r) i)|))
     (54 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (46 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24 (:META META-INTEGERP-CORRECT))
     (16 16 (:REWRITE DEFAULT-FLOOR-2))
     (16 16 (:REWRITE DEFAULT-FLOOR-1))
     (10 10 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
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
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RP::F2-OF-MINUS)
(RP::F2-OF-MINUS-2 (985 985
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (985 985
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (985 985
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (333 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                   (333 37
                        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                   (333 37
                        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                   (333 37
                        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                   (333 37
                        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                   (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                   (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                   (185 37
                        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::SUM-COMM-1-WITH-LOOP-STOPPER)
(RP::SUM-COMM-2-WITH-LOOP-STOPPER
     (47 47 (:REWRITE DEFAULT-PLUS-2))
     (47 47 (:REWRITE DEFAULT-PLUS-1))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::SUM-REORDER (50 50 (:REWRITE DEFAULT-PLUS-2))
                 (50 50 (:REWRITE DEFAULT-PLUS-1))
                 (10 10
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (10 10 (:REWRITE NORMALIZE-ADDENDS))
                 (6 6 (:REWRITE REDUCE-INTEGERP-+))
                 (6 6 (:REWRITE INTEGERP-MINUS-X))
                 (6 6
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                 (6 6 (:META META-INTEGERP-CORRECT))
                 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                 (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::PUSH-ELEMENTS-INTO-F2
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (306 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (294 12 (:REWRITE DEFAULT-FLOOR-RATIO))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (166 118 (:REWRITE DEFAULT-TIMES-2))
     (141 85 (:REWRITE DEFAULT-PLUS-2))
     (136 6 (:REWRITE |(* (if a b c) x)|))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (118 118 (:REWRITE DEFAULT-TIMES-1))
     (118 85 (:REWRITE DEFAULT-PLUS-1))
     (64 64
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (54 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (52 1 (:REWRITE |(floor (+ x r) i)|))
     (46 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (45 2
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (42 3 (:REWRITE |(* (* x y) z)|))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (19 19
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (19 19 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE DEFAULT-FLOOR-2))
     (12 12 (:REWRITE DEFAULT-FLOOR-1))
     (9 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE |(floor x 2)| . 2))
     (8 8 (:REWRITE |(+ c (+ d x))|))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:TYPE-PRESCRIPTION ABS))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
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
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RP::PUSH-ELEMENTS-INTO-D2
     (1471 1471
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1471 1471
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1471 1471
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (280 22 (:REWRITE |(* y x)|))
     (279 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (272 12 (:REWRITE |(* (if a b c) x)|))
     (250 8 (:REWRITE DEFAULT-MOD-RATIO))
     (250 8 (:REWRITE DEFAULT-FLOOR-RATIO))
     (226 146 (:REWRITE DEFAULT-TIMES-2))
     (220 116 (:REWRITE DEFAULT-PLUS-2))
     (170 116 (:REWRITE DEFAULT-PLUS-1))
     (170 34 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (170 34 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (170 34
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (155 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (155 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (151 151
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (151 151
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (151 151
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (151 151
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (146 146 (:REWRITE DEFAULT-TIMES-1))
     (84 6 (:REWRITE |(* (* x y) z)|))
     (70 70
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (52 1 (:REWRITE |(floor (+ x r) i)|))
     (45 2
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (37 37
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (34 34
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (34 34 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (34 34
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (34 34 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (27 27 (:REWRITE INTEGERP-MINUS-X))
     (25 25
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (25 25 (:META META-INTEGERP-CORRECT))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (8 8 (:REWRITE DEFAULT-MOD-1))
     (8 8 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE DEFAULT-FLOOR-1))
     (7 7 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(mod x 2)| . 2))
     (4 4 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:TYPE-PRESCRIPTION ABS))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
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
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RP::SUM-AND-- (60 54 (:REWRITE DEFAULT-PLUS-1))
               (54 54 (:REWRITE DEFAULT-PLUS-2))
               (12 12 (:REWRITE REDUCE-INTEGERP-+))
               (12 12 (:REWRITE INTEGERP-MINUS-X))
               (12 12
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (12 12 (:META META-INTEGERP-CORRECT))
               (8 8 (:REWRITE DEFAULT-MINUS))
               (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
               (5 5 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
               (3 3
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::TYPE-OF-FUNCTIONS (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                       (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                       (9 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                       (9 1
                          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                       (9 1
                          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                       (9 1
                          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                       (9 1
                          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                       (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                       (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                       (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                       (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                       (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                       (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                       (5 1
                          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                       (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                       (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                       (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                       (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                       (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::SUM-OF-THE-SAME-VAR
     (94 82 (:REWRITE DEFAULT-PLUS-1))
     (82 82 (:REWRITE DEFAULT-PLUS-2))
     (24 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (24 24
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 24
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (24 24 (:REWRITE |(equal c (/ x))|))
     (24 24 (:REWRITE |(equal c (- x))|))
     (24 24 (:REWRITE |(equal (/ x) c)|))
     (24 24 (:REWRITE |(equal (/ x) (/ y))|))
     (24 24 (:REWRITE |(equal (- x) c)|))
     (24 24 (:REWRITE |(equal (- x) (- y))|))
     (16 16 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
     (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE O-INFP->NEQ-0))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (8 8 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|)))
(RP::--OF-- (4 4 (:REWRITE DEFAULT-MINUS))
            (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
            (2 2 (:REWRITE REDUCE-INTEGERP-+))
            (2 2 (:REWRITE INTEGERP-MINUS-X))
            (2 2
               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
            (2 2 (:META META-INTEGERP-CORRECT)))
(RP::M2-OF-NEG-LEMMA (816 28 (:REWRITE DEFAULT-MOD-RATIO))
                     (418 40 (:REWRITE |(* y x)|))
                     (374 374
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (374 374
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (374 374
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (370 74 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                     (370 74 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                     (370 74
                          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                     (370 74
                          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                     (354 12 (:REWRITE |(* (if a b c) x)|))
                     (194 194
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (194 194
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (194 194
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (182 32 (:REWRITE |(* (- x) y)|))
                     (178 178 (:REWRITE DEFAULT-TIMES-2))
                     (178 178 (:REWRITE DEFAULT-TIMES-1))
                     (152 40 (:REWRITE DEFAULT-MINUS))
                     (138 6 (:LINEAR MOD-BOUNDS-3))
                     (129 62 (:REWRITE DEFAULT-PLUS-1))
                     (126 62 (:REWRITE DEFAULT-PLUS-2))
                     (120 40 (:REWRITE REDUCE-INTEGERP-+))
                     (104 104
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (74 74 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                     (74 74
                         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                     (74 74 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                     (74 74
                         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                     (74 74 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                     (60 12 (:LINEAR MOD-BOUNDS-2))
                     (40 40
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (40 40 (:META META-INTEGERP-CORRECT))
                     (28 28 (:REWRITE DEFAULT-MOD-2))
                     (28 28 (:REWRITE DEFAULT-MOD-1))
                     (20 20 (:REWRITE |(mod x 2)| . 2))
                     (12 12
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                     (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::M2-SUM-OF-REPEATED-VARS
     (375 18 (:REWRITE DEFAULT-MOD-RATIO))
     (248 248
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (248 248
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (248 248
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (240 48 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (240 48 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (240 48
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (240 48
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (196 25 (:REWRITE |(* y x)|))
     (153 7 (:REWRITE |(* (if a b c) x)|))
     (147 103 (:REWRITE DEFAULT-TIMES-2))
     (103 103 (:REWRITE DEFAULT-TIMES-1))
     (92 4 (:LINEAR MOD-BOUNDS-3))
     (85 85 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (85 85 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (85 85 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (75 39 (:REWRITE DEFAULT-PLUS-2))
     (70 5 (:REWRITE |(* (* x y) z)|))
     (59 39 (:REWRITE DEFAULT-PLUS-1))
     (49 49
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (48 48 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (48 48
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (48 48 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (48 48
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (40 8 (:LINEAR MOD-BOUNDS-2))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (21 21
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (21 21 (:META META-INTEGERP-CORRECT))
     (18 18 (:REWRITE DEFAULT-MOD-2))
     (18 18 (:REWRITE DEFAULT-MOD-1))
     (13 13 (:REWRITE |(mod x 2)| . 2))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1
        (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RP::M2-OF-NEG)
(RP::M2-SUM-OF-SINGLE-VAR (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                          (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                          (75 15
                              (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                          (75 15
                              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                          (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                          (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                          (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                          (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                          (15 15
                              (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                          (15 15 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                          (15 15
                              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                          (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::M2-OF-M2 (1393 34 (:REWRITE DEFAULT-MOD-RATIO))
              (1250 250 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
              (1250 250 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
              (1250 250
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
              (1250 250
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
              (1186 1186
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (1186 1186
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (1186 1186
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (713 149 (:REWRITE DEFAULT-TIMES-2))
              (698 6 (:LINEAR MOD-BOUNDS-3))
              (617 44 (:REWRITE |(* y x)|))
              (545 149 (:REWRITE DEFAULT-TIMES-1))
              (290 34 (:REWRITE DEFAULT-MOD-1))
              (284 12 (:LINEAR MOD-BOUNDS-2))
              (276 22 (:REWRITE |(* (if a b c) x)|))
              (250 250 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
              (250 250
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (250 250
                   (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
              (250 250
                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
              (250 250 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
              (233 233
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (233 233
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (233 233
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (82 82
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (60 24 (:REWRITE DEFAULT-PLUS-2))
              (60 24 (:REWRITE DEFAULT-PLUS-1))
              (36 36 (:REWRITE REDUCE-INTEGERP-+))
              (36 36 (:REWRITE INTEGERP-MINUS-X))
              (36 36
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (36 36 (:META META-INTEGERP-CORRECT))
              (34 34 (:REWRITE DEFAULT-MOD-2))
              (21 21 (:REWRITE |(mod x 2)| . 2))
              (20 1 (:REWRITE SUM-IS-EVEN . 2))
              (11 11
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (11 11 (:REWRITE NORMALIZE-ADDENDS)))
(RP::SUM-OF-VAR-AND-0 (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::M2-WHEN-NOT-TYPE-P (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                        (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                        (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                        (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                        (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                        (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                        (1 1
                           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)))
(RP::F2-WHEN-NOT-TYPE-P (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                        (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                        (9 1
                           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                        (9 1
                           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                        (5 1
                           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                        (5 1
                           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                        (5 1
                           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                        (5 1
                           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::EVENP2-OF-REPEATED-VARS
     (105 49 (:REWRITE DEFAULT-PLUS-2))
     (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (62 49 (:REWRITE DEFAULT-PLUS-1))
     (61 45 (:REWRITE DEFAULT-TIMES-2))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (45 45 (:REWRITE DEFAULT-TIMES-1))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (21 21
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20 (:META META-INTEGERP-CORRECT))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
