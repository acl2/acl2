(RP::AND$-IS-ADDER-AND$)
(RP::OR$-IS-ADDER-OR$)
(RP::SUM-IS-ADDER-B+)
(RP::C-RES-TO-ADDER-SUM)
(RP::C-TO-ADDER-F2
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (828 828
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
     (220 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (182 37 (:REWRITE DEFAULT-PLUS-2))
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
     (166 78 (:REWRITE DEFAULT-TIMES-2))
     (138 37 (:REWRITE DEFAULT-PLUS-1))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (100 22 (:REWRITE REDUCE-INTEGERP-+))
     (100 22 (:META META-INTEGERP-CORRECT))
     (96 78 (:REWRITE DEFAULT-TIMES-1))
     (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (64 64
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (50 2 (:REWRITE |(floor (+ x r) i)|))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (30 30 (:REWRITE NORMALIZE-ADDENDS))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (22 22
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (16 6 (:REWRITE DEFAULT-FLOOR-1))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE |(floor x 2)| . 2))
     (3 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
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
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RP::S-TO-ADDER-M2 (258 8 (:REWRITE DEFAULT-MOD-RATIO))
                   (214 11 (:REWRITE |(* y x)|))
                   (187 187
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (187 187
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (187 187
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (185 37
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (185 37
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (161 3 (:LINEAR MOD-BOUNDS-3))
                   (126 64 (:REWRITE DEFAULT-TIMES-2))
                   (123 123
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (123 123
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (123 123
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (105 5 (:REWRITE SUM-IS-EVEN . 2))
                   (92 18 (:REWRITE DEFAULT-PLUS-2))
                   (92 18 (:REWRITE DEFAULT-PLUS-1))
                   (80 64 (:REWRITE DEFAULT-TIMES-1))
                   (53 53
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (38 6 (:LINEAR MOD-BOUNDS-2))
                   (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                   (37 37
                       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (37 37
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                   (23 23 (:REWRITE REDUCE-INTEGERP-+))
                   (23 23 (:REWRITE INTEGERP-MINUS-X))
                   (23 23
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (23 23 (:META META-INTEGERP-CORRECT))
                   (20 8 (:REWRITE DEFAULT-MOD-1))
                   (11 11
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (11 11 (:REWRITE NORMALIZE-ADDENDS))
                   (8 8 (:REWRITE DEFAULT-MOD-2))
                   (8 8 (:REWRITE |(mod x 2)| . 2))
                   (1 1
                      (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RP::S-SPEC-TO-ADDER-M2 (187 187
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (187 187
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (187 187
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                        (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                        (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                        (185 37
                             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                        (185 37
                             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                        (112 8 (:REWRITE DEFAULT-MOD-RATIO))
                        (84 3 (:LINEAR MOD-BOUNDS-3))
                        (55 11 (:REWRITE |(* y x)|))
                        (49 30 (:REWRITE DEFAULT-TIMES-2))
                        (41 30 (:REWRITE DEFAULT-TIMES-1))
                        (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                        (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                        (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                        (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                        (37 37
                            (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                        (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                        (37 37
                            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                        (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                        (36 6 (:LINEAR MOD-BOUNDS-2))
                        (19 19
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (16 8 (:REWRITE DEFAULT-MOD-1))
                        (11 11 (:REWRITE REDUCE-INTEGERP-+))
                        (11 11 (:REWRITE INTEGERP-MINUS-X))
                        (11 11
                            (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (11 11 (:META META-INTEGERP-CORRECT))
                        (8 8 (:REWRITE DEFAULT-MOD-2))
                        (8 8 (:REWRITE |(mod x 2)| . 2)))
(RP::C-SPEC-TO-ADDER-F2 (828 828
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (828 828
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (828 828
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
                        (84 6 (:REWRITE DEFAULT-FLOOR-RATIO))
                        (78 46 (:REWRITE DEFAULT-TIMES-2))
                        (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                        (60 46 (:REWRITE DEFAULT-TIMES-1))
                        (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                        (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                        (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                        (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                        (32 32
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (20 10 (:REWRITE DEFAULT-PLUS-2))
                        (20 10 (:REWRITE DEFAULT-PLUS-1))
                        (12 6 (:REWRITE DEFAULT-FLOOR-1))
                        (10 10 (:REWRITE REDUCE-INTEGERP-+))
                        (10 10 (:REWRITE INTEGERP-MINUS-X))
                        (10 10
                            (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (10 10 (:META META-INTEGERP-CORRECT))
                        (8 8
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (8 8 (:REWRITE NORMALIZE-ADDENDS))
                        (6 6 (:REWRITE DEFAULT-FLOOR-2))
                        (6 6 (:REWRITE |(floor x 2)| . 2)))
(RP::C-SPEC-TO-ADDER-F2-WITH-HYP
     (912 912
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (912 912
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (912 912
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (342 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (342 38
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (342 38
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (342 38
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (342 38
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (190 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (190 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (190 38
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (84 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (78 46 (:REWRITE DEFAULT-TIMES-2))
     (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (60 46 (:REWRITE DEFAULT-TIMES-1))
     (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (32 32
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 10 (:REWRITE DEFAULT-PLUS-2))
     (20 10 (:REWRITE DEFAULT-PLUS-1))
     (12 6 (:REWRITE DEFAULT-FLOOR-1))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:META META-INTEGERP-CORRECT))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE |(floor x 2)| . 2)))
(RP::C-SPEC-TO-ADDER-F2-WITH-HYP-SIDE-COND
     (5 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::QUARTERNARYP-LEMMA-FOR-ADDER-SUM-0)
(RP::QUARTERNARYP-LEMMA-FOR-ADDER-SUM-1
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (30 6 (:REWRITE RATIONALP-X))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::QUARTERNARYP-LEMMA-FOR-ADDER-SUM-2
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::S-C-SPEC-TO-ADDER-SUM)
(RP::M2-OF-IFIX (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
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
(RP::M2-OF-F2-FOR-ADDER
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::M2-OF-F2-FOR-ADDER-SIDE-COND)
(RP::C-S-SPEC-TO-ADDER-SUM)
(RP::SUM-LIST-TO-ADDER-SUM
     (32 16 (:REWRITE DEFAULT-PLUS-2))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR)))
(RP::ADDER-SUM-COMM1)
(RP::ADDER-SUM-COMM2 (47 47 (:REWRITE DEFAULT-PLUS-2))
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
(RP::ADDER-SUM-REORDER (50 50 (:REWRITE DEFAULT-PLUS-2))
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
(RP::ADDER-ADDER-AND-COMM1)
(RP::ADDER-ADDER-AND-COMM2
     (210 4 (:DEFINITION BITP))
     (93 13 (:REWRITE ACL2-NUMBERP-X))
     (77 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (68 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (40 8 (:REWRITE RATIONALP-X))
     (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (13 13
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION BITP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::B-AND-REORDER (210 4 (:DEFINITION BITP))
                   (93 13 (:REWRITE ACL2-NUMBERP-X))
                   (77 16
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (68 16
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (40 8 (:REWRITE RATIONALP-X))
                   (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                   (13 13
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                   (8 8 (:REWRITE REDUCE-RATIONALP-+))
                   (8 8 (:REWRITE REDUCE-RATIONALP-*))
                   (8 8 (:REWRITE REDUCE-INTEGERP-+))
                   (8 8 (:REWRITE RATIONALP-MINUS-X))
                   (8 8
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (8 8 (:REWRITE INTEGERP-MINUS-X))
                   (8 8
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (8 8 (:META META-RATIONALP-CORRECT))
                   (8 8 (:META META-INTEGERP-CORRECT))
                   (4 4 (:TYPE-PRESCRIPTION BITP))
                   (4 4
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::B-OR-COMM1)
(RP::B-OR-COMM2 (210 4 (:DEFINITION BITP))
                (93 13 (:REWRITE ACL2-NUMBERP-X))
                (77 16
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (68 16
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (40 8 (:REWRITE RATIONALP-X))
                (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                (16 8 (:REWRITE O-INFP->NEQ-0))
                (13 13
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (12 12
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (8 8 (:REWRITE REDUCE-RATIONALP-+))
                (8 8 (:REWRITE REDUCE-RATIONALP-*))
                (8 8 (:REWRITE REDUCE-INTEGERP-+))
                (8 8 (:REWRITE RATIONALP-MINUS-X))
                (8 8
                   (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (8 8 (:REWRITE INTEGERP-MINUS-X))
                (8 8
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (8 8 (:META META-RATIONALP-CORRECT))
                (8 8 (:META META-INTEGERP-CORRECT))
                (4 4 (:TYPE-PRESCRIPTION BITP)))
(RP::B-OR-REORDER (210 4 (:DEFINITION BITP))
                  (93 13 (:REWRITE ACL2-NUMBERP-X))
                  (77 16
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (68 16
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (40 8 (:REWRITE RATIONALP-X))
                  (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                  (16 8 (:REWRITE O-INFP->NEQ-0))
                  (13 13
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (12 12
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (8 8 (:REWRITE REDUCE-RATIONALP-+))
                  (8 8 (:REWRITE REDUCE-RATIONALP-*))
                  (8 8 (:REWRITE REDUCE-INTEGERP-+))
                  (8 8 (:REWRITE RATIONALP-MINUS-X))
                  (8 8
                     (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (8 8 (:REWRITE INTEGERP-MINUS-X))
                  (8 8
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (8 8 (:META META-RATIONALP-CORRECT))
                  (8 8 (:META META-INTEGERP-CORRECT))
                  (4 4 (:TYPE-PRESCRIPTION BITP)))
(RP::EQUAL-OF-ADDER-AND-F2
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (30 6 (:REWRITE RATIONALP-X))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::MERGE-ADDER-SUM-IS-ADDER-SUM)
(RP::BIN-XOR-IS-S (125 25 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                  (125 25 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                  (125 25
                       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                  (125 25
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                  (122 122
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (122 122
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (122 122
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (78 6
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (72 12 (:REWRITE ACL2-NUMBERP-X))
                  (56 4 (:REWRITE DEFAULT-MOD-RATIO))
                  (56 2 (:LINEAR MOD-BOUNDS-3))
                  (30 6 (:REWRITE RATIONALP-X))
                  (30 6 (:REWRITE |(* y x)|))
                  (26 16 (:REWRITE DEFAULT-TIMES-2))
                  (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                  (25 25
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                  (25 25 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                  (25 25
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                  (25 25 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                  (24 4 (:LINEAR MOD-BOUNDS-2))
                  (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (22 16 (:REWRITE DEFAULT-TIMES-1))
                  (18 6
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (18 3 (:REWRITE O-INFP->NEQ-0))
                  (12 12 (:REWRITE REDUCE-INTEGERP-+))
                  (12 12 (:REWRITE INTEGERP-MINUS-X))
                  (12 12
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (12 12
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (12 12 (:META META-INTEGERP-CORRECT))
                  (10 10
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (9 9 (:TYPE-PRESCRIPTION O-FINP))
                  (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                  (8 4 (:REWRITE DEFAULT-MOD-1))
                  (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (6 6 (:REWRITE REDUCE-RATIONALP-+))
                  (6 6 (:REWRITE REDUCE-RATIONALP-*))
                  (6 6
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (6 6
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (6 6 (:REWRITE RATIONALP-MINUS-X))
                  (6 6
                     (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (6 6
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (6 6 (:REWRITE |(equal c (/ x))|))
                  (6 6 (:REWRITE |(equal c (- x))|))
                  (6 6 (:REWRITE |(equal (/ x) c)|))
                  (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                  (6 6 (:REWRITE |(equal (- x) c)|))
                  (6 6 (:REWRITE |(equal (- x) (- y))|))
                  (6 6 (:META META-RATIONALP-CORRECT))
                  (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                  (4 4 (:REWRITE DEFAULT-MOD-2))
                  (4 4 (:REWRITE |(mod x 2)| . 2))
                  (3 3
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIN-XOR-IS-S-SC (78 6
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (72 12 (:REWRITE ACL2-NUMBERP-X))
                     (30 6 (:REWRITE RATIONALP-X))
                     (18 6
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (18 3 (:REWRITE O-INFP->NEQ-0))
                     (12 12
                         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (9 9 (:TYPE-PRESCRIPTION O-FINP))
                     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (6 6 (:REWRITE REDUCE-RATIONALP-+))
                     (6 6 (:REWRITE REDUCE-RATIONALP-*))
                     (6 6
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (6 6 (:REWRITE REDUCE-INTEGERP-+))
                     (6 6
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (6 6 (:REWRITE RATIONALP-MINUS-X))
                     (6 6
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (6 6 (:REWRITE INTEGERP-MINUS-X))
                     (6 6
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (6 6
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (6 6 (:REWRITE |(equal c (/ x))|))
                     (6 6 (:REWRITE |(equal c (- x))|))
                     (6 6 (:REWRITE |(equal (/ x) c)|))
                     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                     (6 6 (:REWRITE |(equal (- x) c)|))
                     (6 6 (:REWRITE |(equal (- x) (- y))|))
                     (6 6 (:META META-RATIONALP-CORRECT))
                     (6 6 (:META META-INTEGERP-CORRECT))
                     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIN-AND-IS-C (587 587
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (587 587
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (587 587
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (225 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (225 25
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (225 25
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (225 25
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (225 25
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (125 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (125 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (125 25
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (78 6
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (72 12 (:REWRITE ACL2-NUMBERP-X))
                  (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                  (60 36 (:REWRITE DEFAULT-TIMES-2))
                  (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                  (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                  (48 36 (:REWRITE DEFAULT-TIMES-1))
                  (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (30 6 (:REWRITE RATIONALP-X))
                  (24 24
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (18 8 (:REWRITE DEFAULT-PLUS-2))
                  (18 8 (:REWRITE DEFAULT-PLUS-1))
                  (18 6
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (18 3 (:REWRITE O-INFP->NEQ-0))
                  (14 14 (:REWRITE REDUCE-INTEGERP-+))
                  (14 14 (:REWRITE INTEGERP-MINUS-X))
                  (14 14
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (14 14 (:META META-INTEGERP-CORRECT))
                  (12 12
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (9 9 (:TYPE-PRESCRIPTION O-FINP))
                  (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                  (8 4 (:REWRITE DEFAULT-FLOOR-1))
                  (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (6 6 (:REWRITE REDUCE-RATIONALP-+))
                  (6 6 (:REWRITE REDUCE-RATIONALP-*))
                  (6 6
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (6 6
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (6 6 (:REWRITE RATIONALP-MINUS-X))
                  (6 6
                     (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (6 6
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (6 6 (:REWRITE NORMALIZE-ADDENDS))
                  (6 6
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (6 6 (:REWRITE |(equal c (/ x))|))
                  (6 6 (:REWRITE |(equal c (- x))|))
                  (6 6 (:REWRITE |(equal (/ x) c)|))
                  (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                  (6 6 (:REWRITE |(equal (- x) c)|))
                  (6 6 (:REWRITE |(equal (- x) (- y))|))
                  (6 6 (:META META-RATIONALP-CORRECT))
                  (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                  (4 4 (:REWRITE DEFAULT-FLOOR-2))
                  (4 4 (:REWRITE |(floor x 2)| . 2))
                  (3 3
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIN-AND-IS-C-1 (78 6
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (72 12 (:REWRITE ACL2-NUMBERP-X))
                    (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (30 6 (:REWRITE RATIONALP-X))
                    (18 6
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (18 3 (:REWRITE O-INFP->NEQ-0))
                    (12 12
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (9 9 (:TYPE-PRESCRIPTION O-FINP))
                    (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                    (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (6 6 (:REWRITE REDUCE-RATIONALP-+))
                    (6 6 (:REWRITE REDUCE-RATIONALP-*))
                    (6 6
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (6 6 (:REWRITE REDUCE-INTEGERP-+))
                    (6 6
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (6 6 (:REWRITE RATIONALP-MINUS-X))
                    (6 6
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (6 6 (:REWRITE INTEGERP-MINUS-X))
                    (6 6
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (6 6
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (6 6 (:REWRITE |(equal c (/ x))|))
                    (6 6 (:REWRITE |(equal c (- x))|))
                    (6 6 (:REWRITE |(equal (/ x) c)|))
                    (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                    (6 6 (:REWRITE |(equal (- x) c)|))
                    (6 6 (:REWRITE |(equal (- x) (- y))|))
                    (6 6 (:META META-RATIONALP-CORRECT))
                    (6 6 (:META META-INTEGERP-CORRECT))
                    (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                    (3 3
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIN-AND-IS-C-2 (78 6
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (72 12 (:REWRITE ACL2-NUMBERP-X))
                    (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (30 6 (:REWRITE RATIONALP-X))
                    (18 6
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (18 3 (:REWRITE O-INFP->NEQ-0))
                    (12 12
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (9 9 (:TYPE-PRESCRIPTION O-FINP))
                    (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                    (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (6 6 (:REWRITE REDUCE-RATIONALP-+))
                    (6 6 (:REWRITE REDUCE-RATIONALP-*))
                    (6 6
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (6 6 (:REWRITE REDUCE-INTEGERP-+))
                    (6 6
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (6 6 (:REWRITE RATIONALP-MINUS-X))
                    (6 6
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (6 6 (:REWRITE INTEGERP-MINUS-X))
                    (6 6
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (6 6
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (6 6 (:REWRITE |(equal c (/ x))|))
                    (6 6 (:REWRITE |(equal c (- x))|))
                    (6 6 (:REWRITE |(equal (/ x) c)|))
                    (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                    (6 6 (:REWRITE |(equal (- x) c)|))
                    (6 6 (:REWRITE |(equal (- x) (- y))|))
                    (6 6 (:META META-RATIONALP-CORRECT))
                    (6 6 (:META META-INTEGERP-CORRECT))
                    (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                    (3 3
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIN-AND-IS-C-SC (78 6
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (72 12 (:REWRITE ACL2-NUMBERP-X))
                     (30 6 (:REWRITE RATIONALP-X))
                     (18 6
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (18 3 (:REWRITE O-INFP->NEQ-0))
                     (12 12
                         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (9 9 (:TYPE-PRESCRIPTION O-FINP))
                     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (6 6 (:REWRITE REDUCE-RATIONALP-+))
                     (6 6 (:REWRITE REDUCE-RATIONALP-*))
                     (6 6
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (6 6 (:REWRITE REDUCE-INTEGERP-+))
                     (6 6
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (6 6 (:REWRITE RATIONALP-MINUS-X))
                     (6 6
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (6 6 (:REWRITE INTEGERP-MINUS-X))
                     (6 6
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (6 6
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (6 6 (:REWRITE |(equal c (/ x))|))
                     (6 6 (:REWRITE |(equal c (- x))|))
                     (6 6 (:REWRITE |(equal (/ x) c)|))
                     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                     (6 6 (:REWRITE |(equal (- x) c)|))
                     (6 6 (:REWRITE |(equal (- x) (- y))|))
                     (6 6 (:META META-RATIONALP-CORRECT))
                     (6 6 (:META META-INTEGERP-CORRECT))
                     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::C-OF-SAME-C)
(RP::BIN-OR-P1 (819 819
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (819 819
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (819 819
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (297 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (297 33
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (297 33
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
               (297 33
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
               (297 33
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (182 14
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (168 28 (:REWRITE ACL2-NUMBERP-X))
               (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
               (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
               (165 33
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (70 14 (:REWRITE RATIONALP-X))
               (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
               (60 36 (:REWRITE DEFAULT-TIMES-2))
               (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
               (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
               (48 36 (:REWRITE DEFAULT-TIMES-1))
               (42 14
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (42 7 (:REWRITE O-INFP->NEQ-0))
               (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (28 28
                   (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
               (24 24
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (22 22 (:REWRITE REDUCE-INTEGERP-+))
               (22 22 (:REWRITE INTEGERP-MINUS-X))
               (22 22
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (22 22 (:META META-INTEGERP-CORRECT))
               (21 21 (:TYPE-PRESCRIPTION O-FINP))
               (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
               (18 8 (:REWRITE DEFAULT-PLUS-2))
               (18 8 (:REWRITE DEFAULT-PLUS-1))
               (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (14 14 (:REWRITE REDUCE-RATIONALP-+))
               (14 14 (:REWRITE REDUCE-RATIONALP-*))
               (14 14
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (14 14
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (14 14 (:REWRITE RATIONALP-MINUS-X))
               (14 14
                   (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
               (14 14
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (14 14 (:REWRITE |(equal c (/ x))|))
               (14 14 (:REWRITE |(equal c (- x))|))
               (14 14 (:REWRITE |(equal (/ x) c)|))
               (14 14 (:REWRITE |(equal (/ x) (/ y))|))
               (14 14 (:REWRITE |(equal (- x) c)|))
               (14 14 (:REWRITE |(equal (- x) (- y))|))
               (14 14 (:META META-RATIONALP-CORRECT))
               (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
               (8 4 (:REWRITE DEFAULT-FLOOR-1))
               (7 7
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (6 6
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (6 6 (:REWRITE NORMALIZE-ADDENDS))
               (4 4 (:REWRITE DEFAULT-FLOOR-2))
               (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P1A (819 819
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (819 819
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (819 819
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (297 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (182 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (168 28 (:REWRITE ACL2-NUMBERP-X))
                (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (70 14 (:REWRITE RATIONALP-X))
                (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                (60 36 (:REWRITE DEFAULT-TIMES-2))
                (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                (48 36 (:REWRITE DEFAULT-TIMES-1))
                (42 14
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (42 7 (:REWRITE O-INFP->NEQ-0))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (28 28
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (24 24
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (22 22 (:REWRITE REDUCE-INTEGERP-+))
                (22 22 (:REWRITE INTEGERP-MINUS-X))
                (22 22
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (22 22 (:META META-INTEGERP-CORRECT))
                (21 21 (:TYPE-PRESCRIPTION O-FINP))
                (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                (18 8 (:REWRITE DEFAULT-PLUS-2))
                (18 8 (:REWRITE DEFAULT-PLUS-1))
                (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (14 14 (:REWRITE REDUCE-RATIONALP-+))
                (14 14 (:REWRITE REDUCE-RATIONALP-*))
                (14 14
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (14 14
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (14 14 (:REWRITE RATIONALP-MINUS-X))
                (14 14
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (14 14
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (14 14 (:REWRITE |(equal c (/ x))|))
                (14 14 (:REWRITE |(equal c (- x))|))
                (14 14 (:REWRITE |(equal (/ x) c)|))
                (14 14 (:REWRITE |(equal (/ x) (/ y))|))
                (14 14 (:REWRITE |(equal (- x) c)|))
                (14 14 (:REWRITE |(equal (- x) (- y))|))
                (14 14 (:META META-RATIONALP-CORRECT))
                (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (8 4 (:REWRITE DEFAULT-FLOOR-1))
                (7 7
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P1B (767 767
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (767 767
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (767 767
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (297 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (182 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (168 28 (:REWRITE ACL2-NUMBERP-X))
                (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (70 14 (:REWRITE RATIONALP-X))
                (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                (60 36 (:REWRITE DEFAULT-TIMES-2))
                (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                (48 36 (:REWRITE DEFAULT-TIMES-1))
                (42 14
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (42 7 (:REWRITE O-INFP->NEQ-0))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (28 28
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (24 24
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (22 22 (:REWRITE REDUCE-INTEGERP-+))
                (22 22 (:REWRITE INTEGERP-MINUS-X))
                (22 22
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (22 22 (:META META-INTEGERP-CORRECT))
                (21 21 (:TYPE-PRESCRIPTION O-FINP))
                (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                (18 8 (:REWRITE DEFAULT-PLUS-2))
                (18 8 (:REWRITE DEFAULT-PLUS-1))
                (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (14 14 (:REWRITE REDUCE-RATIONALP-+))
                (14 14 (:REWRITE REDUCE-RATIONALP-*))
                (14 14
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (14 14
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (14 14 (:REWRITE RATIONALP-MINUS-X))
                (14 14
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (14 14
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (14 14 (:REWRITE |(equal c (/ x))|))
                (14 14 (:REWRITE |(equal c (- x))|))
                (14 14 (:REWRITE |(equal (/ x) c)|))
                (14 14 (:REWRITE |(equal (/ x) (/ y))|))
                (14 14 (:REWRITE |(equal (- x) c)|))
                (14 14 (:REWRITE |(equal (- x) (- y))|))
                (14 14 (:META META-RATIONALP-CORRECT))
                (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (8 4 (:REWRITE DEFAULT-FLOOR-1))
                (7 7
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P1B-V2 (185 15
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (168 28 (:REWRITE ACL2-NUMBERP-X))
                   (70 14 (:REWRITE RATIONALP-X))
                   (45 15
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (42 7 (:REWRITE O-INFP->NEQ-0))
                   (28 28
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                   (21 21 (:TYPE-PRESCRIPTION O-FINP))
                   (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                   (17 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                   (14 14 (:REWRITE REDUCE-RATIONALP-+))
                   (14 14 (:REWRITE REDUCE-RATIONALP-*))
                   (14 14 (:REWRITE REDUCE-INTEGERP-+))
                   (14 14 (:REWRITE RATIONALP-MINUS-X))
                   (14 14
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (14 14 (:REWRITE INTEGERP-MINUS-X))
                   (14 14
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (14 14 (:META META-RATIONALP-CORRECT))
                   (14 14 (:META META-INTEGERP-CORRECT))
                   (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                   (7 7
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (3 3
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (3 3 (:REWRITE NORMALIZE-ADDENDS))
                   (3 3 (:REWRITE DEFAULT-PLUS-2))
                   (3 3 (:REWRITE DEFAULT-PLUS-1))
                   (1 1 (:REWRITE FOLD-CONSTS-IN-+))
                   (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::BIN-OR-P1B-V3 (185 15
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (168 28 (:REWRITE ACL2-NUMBERP-X))
                   (70 14 (:REWRITE RATIONALP-X))
                   (45 15
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (42 7 (:REWRITE O-INFP->NEQ-0))
                   (28 28
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                   (21 21 (:TYPE-PRESCRIPTION O-FINP))
                   (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                   (17 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                   (14 14 (:REWRITE REDUCE-RATIONALP-+))
                   (14 14 (:REWRITE REDUCE-RATIONALP-*))
                   (14 14 (:REWRITE REDUCE-INTEGERP-+))
                   (14 14 (:REWRITE RATIONALP-MINUS-X))
                   (14 14
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (14 14 (:REWRITE INTEGERP-MINUS-X))
                   (14 14
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (14 14 (:META META-RATIONALP-CORRECT))
                   (14 14 (:META META-INTEGERP-CORRECT))
                   (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                   (7 7
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (3 3
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (3 3 (:REWRITE NORMALIZE-ADDENDS))
                   (3 3 (:REWRITE DEFAULT-PLUS-2))
                   (3 3 (:REWRITE DEFAULT-PLUS-1))
                   (1 1 (:REWRITE FOLD-CONSTS-IN-+))
                   (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::BIN-OR-P1C (819 819
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (819 819
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (819 819
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (297 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (182 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (168 28 (:REWRITE ACL2-NUMBERP-X))
                (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (165 33
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (70 14 (:REWRITE RATIONALP-X))
                (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                (60 36 (:REWRITE DEFAULT-TIMES-2))
                (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                (48 36 (:REWRITE DEFAULT-TIMES-1))
                (42 14
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (42 7 (:REWRITE O-INFP->NEQ-0))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (28 28
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (24 24
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (22 22 (:REWRITE REDUCE-INTEGERP-+))
                (22 22 (:REWRITE INTEGERP-MINUS-X))
                (22 22
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (22 22 (:META META-INTEGERP-CORRECT))
                (21 21 (:TYPE-PRESCRIPTION O-FINP))
                (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                (18 8 (:REWRITE DEFAULT-PLUS-2))
                (18 8 (:REWRITE DEFAULT-PLUS-1))
                (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (14 14 (:REWRITE REDUCE-RATIONALP-+))
                (14 14 (:REWRITE REDUCE-RATIONALP-*))
                (14 14
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (14 14
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (14 14 (:REWRITE RATIONALP-MINUS-X))
                (14 14
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (14 14
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (14 14 (:REWRITE |(equal c (/ x))|))
                (14 14 (:REWRITE |(equal c (- x))|))
                (14 14 (:REWRITE |(equal (/ x) c)|))
                (14 14 (:REWRITE |(equal (/ x) (/ y))|))
                (14 14 (:REWRITE |(equal (- x) c)|))
                (14 14 (:REWRITE |(equal (- x) (- y))|))
                (14 14 (:META META-RATIONALP-CORRECT))
                (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (8 4 (:REWRITE DEFAULT-FLOOR-1))
                (7 7
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P2A (1155 1155
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1155 1155
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (1155 1155
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (441 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (390 30
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (360 60 (:REWRITE ACL2-NUMBERP-X))
                (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (150 30 (:REWRITE RATIONALP-X))
                (90 30
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (90 15 (:REWRITE O-INFP->NEQ-0))
                (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                (60 60
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (60 36 (:REWRITE DEFAULT-TIMES-2))
                (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                (48 36 (:REWRITE DEFAULT-TIMES-1))
                (45 45 (:TYPE-PRESCRIPTION O-FINP))
                (45 15 (:REWRITE O-FIRST-EXPT-O-INFP))
                (38 38 (:REWRITE REDUCE-INTEGERP-+))
                (38 38 (:REWRITE INTEGERP-MINUS-X))
                (38 38
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (38 38 (:META META-INTEGERP-CORRECT))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (30 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (30 30 (:REWRITE REDUCE-RATIONALP-+))
                (30 30 (:REWRITE REDUCE-RATIONALP-*))
                (30 30
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (30 30
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (30 30 (:REWRITE RATIONALP-MINUS-X))
                (30 30
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (30 30
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (30 30 (:REWRITE |(equal c (/ x))|))
                (30 30 (:REWRITE |(equal c (- x))|))
                (30 30 (:REWRITE |(equal (/ x) c)|))
                (30 30 (:REWRITE |(equal (/ x) (/ y))|))
                (30 30 (:REWRITE |(equal (- x) c)|))
                (30 30 (:REWRITE |(equal (- x) (- y))|))
                (30 30 (:META META-RATIONALP-CORRECT))
                (30 15 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (24 24
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (18 8 (:REWRITE DEFAULT-PLUS-2))
                (18 8 (:REWRITE DEFAULT-PLUS-1))
                (15 15
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (8 4 (:REWRITE DEFAULT-FLOOR-1))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P2B (1827 1827
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1827 1827
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (1827 1827
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (806 62
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (744 124 (:REWRITE ACL2-NUMBERP-X))
                (729 81 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (729 81
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (729 81
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (729 81
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (729 81
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (405 81 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (405 81 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (405 81
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (310 62 (:REWRITE RATIONALP-X))
                (186 62
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (186 31 (:REWRITE O-INFP->NEQ-0))
                (124 124
                     (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (93 93 (:TYPE-PRESCRIPTION O-FINP))
                (93 31 (:REWRITE O-FIRST-EXPT-O-INFP))
                (70 70 (:REWRITE REDUCE-INTEGERP-+))
                (70 70 (:REWRITE INTEGERP-MINUS-X))
                (70 70
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (70 70 (:META META-INTEGERP-CORRECT))
                (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                (62 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (62 62 (:REWRITE REDUCE-RATIONALP-+))
                (62 62 (:REWRITE REDUCE-RATIONALP-*))
                (62 62
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (62 62
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (62 62 (:REWRITE RATIONALP-MINUS-X))
                (62 62
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (62 62
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (62 62 (:REWRITE |(equal c (/ x))|))
                (62 62 (:REWRITE |(equal c (- x))|))
                (62 62 (:REWRITE |(equal (/ x) c)|))
                (62 62 (:REWRITE |(equal (/ x) (/ y))|))
                (62 62 (:REWRITE |(equal (- x) c)|))
                (62 62 (:REWRITE |(equal (- x) (- y))|))
                (62 62 (:META META-RATIONALP-CORRECT))
                (62 31 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (60 36 (:REWRITE DEFAULT-TIMES-2))
                (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                (48 36 (:REWRITE DEFAULT-TIMES-1))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (31 31
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (24 24
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (18 8 (:REWRITE DEFAULT-PLUS-2))
                (18 8 (:REWRITE DEFAULT-PLUS-1))
                (8 4 (:REWRITE DEFAULT-FLOOR-1))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P2C (1155 1155
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1155 1155
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (1155 1155
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (441 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (390 30
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (360 60 (:REWRITE ACL2-NUMBERP-X))
                (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (245 49
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (150 30 (:REWRITE RATIONALP-X))
                (90 30
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (90 15 (:REWRITE O-INFP->NEQ-0))
                (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                (60 60
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (60 36 (:REWRITE DEFAULT-TIMES-2))
                (56 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                (48 36 (:REWRITE DEFAULT-TIMES-1))
                (45 45 (:TYPE-PRESCRIPTION O-FINP))
                (45 15 (:REWRITE O-FIRST-EXPT-O-INFP))
                (38 38 (:REWRITE REDUCE-INTEGERP-+))
                (38 38 (:REWRITE INTEGERP-MINUS-X))
                (38 38
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (38 38 (:META META-INTEGERP-CORRECT))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (30 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (30 30 (:REWRITE REDUCE-RATIONALP-+))
                (30 30 (:REWRITE REDUCE-RATIONALP-*))
                (30 30
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (30 30
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (30 30 (:REWRITE RATIONALP-MINUS-X))
                (30 30
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (30 30
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (30 30 (:REWRITE |(equal c (/ x))|))
                (30 30 (:REWRITE |(equal c (- x))|))
                (30 30 (:REWRITE |(equal (/ x) c)|))
                (30 30 (:REWRITE |(equal (/ x) (/ y))|))
                (30 30 (:REWRITE |(equal (- x) c)|))
                (30 30 (:REWRITE |(equal (- x) (- y))|))
                (30 30 (:META META-RATIONALP-CORRECT))
                (30 15 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (24 24
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (18 8 (:REWRITE DEFAULT-PLUS-2))
                (18 8 (:REWRITE DEFAULT-PLUS-1))
                (15 15
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (8 4 (:REWRITE DEFAULT-FLOOR-1))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P3 (2650 2650
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (2650 2650
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (2650 2650
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (1026 114 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (1026 114
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (1026 114
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
               (1026 114
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
               (1026 114
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (738 78
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (648 108 (:REWRITE ACL2-NUMBERP-X))
               (570 114 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
               (570 114 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
               (570 114
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (270 54 (:REWRITE RATIONALP-X))
               (198 78
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (138 39 (:REWRITE O-INFP->NEQ-0))
               (108 108
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
               (78 78 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (78 78
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (78 78
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (78 78
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (78 78 (:REWRITE |(equal c (/ x))|))
               (78 78 (:REWRITE |(equal c (- x))|))
               (78 78 (:REWRITE |(equal (/ x) c)|))
               (78 78 (:REWRITE |(equal (/ x) (/ y))|))
               (78 78 (:REWRITE |(equal (- x) c)|))
               (78 78 (:REWRITE |(equal (- x) (- y))|))
               (54 54 (:REWRITE REDUCE-RATIONALP-+))
               (54 54 (:REWRITE REDUCE-RATIONALP-*))
               (54 54 (:REWRITE REDUCE-INTEGERP-+))
               (54 54 (:REWRITE RATIONALP-MINUS-X))
               (54 54
                   (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
               (54 54 (:REWRITE INTEGERP-MINUS-X))
               (54 54
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (54 54 (:META META-RATIONALP-CORRECT))
               (54 54 (:META META-INTEGERP-CORRECT))
               (51 51
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (45 45 (:TYPE-PRESCRIPTION O-FINP))
               (45 15 (:REWRITE O-FIRST-EXPT-O-INFP))
               (30 15 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::OR-OF-AND-OF-THE-SAME
     (208 4 (:DEFINITION BITP))
     (92 12 (:REWRITE ACL2-NUMBERP-X))
     (76 15
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (65 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (40 8 (:REWRITE RATIONALP-X))
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
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:TYPE-PRESCRIPTION BITP))
     (4 2 (:REWRITE O-INFP->NEQ-0)))
(RP::BIN-OR-P2-SC (1374 1374
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (1374 1374
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (1374 1374
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (558 62 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (558 62
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (558 62
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (558 62
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (558 62
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (390 30
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (360 60 (:REWRITE ACL2-NUMBERP-X))
                  (310 62 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (310 62 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (310 62
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (150 30 (:REWRITE RATIONALP-X))
                  (132 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                  (120 72 (:REWRITE DEFAULT-TIMES-2))
                  (112 8 (:REWRITE DEFAULT-FLOOR-RATIO))
                  (112 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                  (96 72 (:REWRITE DEFAULT-TIMES-1))
                  (90 30
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (90 15 (:REWRITE O-INFP->NEQ-0))
                  (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (60 60
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (48 48
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (46 46 (:REWRITE REDUCE-INTEGERP-+))
                  (46 46 (:REWRITE INTEGERP-MINUS-X))
                  (46 46
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (46 46 (:META META-INTEGERP-CORRECT))
                  (45 45 (:TYPE-PRESCRIPTION O-FINP))
                  (45 15 (:REWRITE O-FIRST-EXPT-O-INFP))
                  (36 16 (:REWRITE DEFAULT-PLUS-2))
                  (36 16 (:REWRITE DEFAULT-PLUS-1))
                  (30 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (30 30 (:REWRITE REDUCE-RATIONALP-+))
                  (30 30 (:REWRITE REDUCE-RATIONALP-*))
                  (30 30
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (30 30
                      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (30 30 (:REWRITE RATIONALP-MINUS-X))
                  (30 30
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (30 30
                      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (30 30 (:REWRITE |(equal c (/ x))|))
                  (30 30 (:REWRITE |(equal c (- x))|))
                  (30 30 (:REWRITE |(equal (/ x) c)|))
                  (30 30 (:REWRITE |(equal (/ x) (/ y))|))
                  (30 30 (:REWRITE |(equal (- x) c)|))
                  (30 30 (:REWRITE |(equal (- x) (- y))|))
                  (30 30 (:META META-RATIONALP-CORRECT))
                  (30 15 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                  (16 8 (:REWRITE DEFAULT-FLOOR-1))
                  (15 15
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (12 12
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (12 12 (:REWRITE NORMALIZE-ADDENDS))
                  (8 8 (:REWRITE DEFAULT-FLOOR-2))
                  (8 8 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P2-V2-SC
     (2382 2382
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2382 2382
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2382 2382
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (990 110 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (990 110
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (990 110
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (990 110
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (990 110
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (806 62
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (744 124 (:REWRITE ACL2-NUMBERP-X))
     (550 110 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (550 110 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (550 110
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (310 62 (:REWRITE RATIONALP-X))
     (186 62
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (186 31 (:REWRITE O-INFP->NEQ-0))
     (132 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (124 124
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (120 72 (:REWRITE DEFAULT-TIMES-2))
     (112 8 (:REWRITE DEFAULT-FLOOR-RATIO))
     (112 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (96 72 (:REWRITE DEFAULT-TIMES-1))
     (93 93 (:TYPE-PRESCRIPTION O-FINP))
     (93 31 (:REWRITE O-FIRST-EXPT-O-INFP))
     (78 78 (:REWRITE REDUCE-INTEGERP-+))
     (78 78 (:REWRITE INTEGERP-MINUS-X))
     (78 78
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (78 78 (:META META-INTEGERP-CORRECT))
     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (62 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (62 62 (:REWRITE REDUCE-RATIONALP-+))
     (62 62 (:REWRITE REDUCE-RATIONALP-*))
     (62 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (62 62 (:REWRITE RATIONALP-MINUS-X))
     (62 62
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (62 62
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (62 62 (:REWRITE |(equal c (/ x))|))
     (62 62 (:REWRITE |(equal c (- x))|))
     (62 62 (:REWRITE |(equal (/ x) c)|))
     (62 62 (:REWRITE |(equal (/ x) (/ y))|))
     (62 62 (:REWRITE |(equal (- x) c)|))
     (62 62 (:REWRITE |(equal (- x) (- y))|))
     (62 62 (:META META-RATIONALP-CORRECT))
     (62 31 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (48 48
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (36 16 (:REWRITE DEFAULT-PLUS-2))
     (36 16 (:REWRITE DEFAULT-PLUS-1))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 8 (:REWRITE DEFAULT-FLOOR-1))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE |(floor x 2)| . 2)))
(RP::BIN-OR-P1-SC (870 870
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (870 870
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (870 870
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (342 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (342 38
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (342 38
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (342 38
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (342 38
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (190 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (190 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (190 38
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (182 14
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (168 28 (:REWRITE ACL2-NUMBERP-X))
                  (132 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                  (120 72 (:REWRITE DEFAULT-TIMES-2))
                  (112 8 (:REWRITE DEFAULT-FLOOR-RATIO))
                  (112 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                  (96 72 (:REWRITE DEFAULT-TIMES-1))
                  (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (70 14 (:REWRITE RATIONALP-X))
                  (48 48
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (42 14
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (42 7 (:REWRITE O-INFP->NEQ-0))
                  (36 16 (:REWRITE DEFAULT-PLUS-2))
                  (36 16 (:REWRITE DEFAULT-PLUS-1))
                  (30 30 (:REWRITE REDUCE-INTEGERP-+))
                  (30 30 (:REWRITE INTEGERP-MINUS-X))
                  (30 30
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (30 30 (:META META-INTEGERP-CORRECT))
                  (28 28
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (21 21 (:TYPE-PRESCRIPTION O-FINP))
                  (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                  (16 8 (:REWRITE DEFAULT-FLOOR-1))
                  (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (14 14 (:REWRITE REDUCE-RATIONALP-+))
                  (14 14 (:REWRITE REDUCE-RATIONALP-*))
                  (14 14
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (14 14
                      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (14 14 (:REWRITE RATIONALP-MINUS-X))
                  (14 14
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (14 14
                      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (14 14 (:REWRITE |(equal c (/ x))|))
                  (14 14 (:REWRITE |(equal c (- x))|))
                  (14 14 (:REWRITE |(equal (/ x) c)|))
                  (14 14 (:REWRITE |(equal (/ x) (/ y))|))
                  (14 14 (:REWRITE |(equal (- x) c)|))
                  (14 14 (:REWRITE |(equal (- x) (- y))|))
                  (14 14 (:META META-RATIONALP-CORRECT))
                  (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                  (12 12
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (12 12 (:REWRITE NORMALIZE-ADDENDS))
                  (8 8 (:REWRITE DEFAULT-FLOOR-2))
                  (8 8 (:REWRITE |(floor x 2)| . 2))
                  (7 7
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::ADDER-SUM-OF-0)
(RP::ADDER-TYPE-FIX)
(RP::M2-OF-ADDER-SUM-M2 (584 22 (:REWRITE DEFAULT-MOD-RATIO))
                        (245 17 (:REWRITE |(* (if a b c) x)|))
                        (238 31 (:REWRITE |(* y x)|))
                        (199 199
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (199 199
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (199 199
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                        (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                        (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                        (185 37
                             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                        (185 37
                             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                        (181 181
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                        (181 181
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                        (181 181
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                        (167 110 (:REWRITE DEFAULT-TIMES-1))
                        (129 110 (:REWRITE DEFAULT-TIMES-2))
                        (84 3 (:LINEAR MOD-BOUNDS-3))
                        (61 61
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (60 24 (:REWRITE DEFAULT-PLUS-2))
                        (60 24 (:REWRITE DEFAULT-PLUS-1))
                        (52 22 (:REWRITE DEFAULT-MOD-1))
                        (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                        (37 37
                            (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                        (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                        (37 37
                            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                        (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                        (36 6 (:LINEAR MOD-BOUNDS-2))
                        (23 23 (:REWRITE REDUCE-INTEGERP-+))
                        (23 23 (:REWRITE INTEGERP-MINUS-X))
                        (23 23
                            (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (23 23 (:META META-INTEGERP-CORRECT))
                        (22 22 (:REWRITE DEFAULT-MOD-2))
                        (20 1 (:REWRITE SUM-IS-EVEN . 2))
                        (13 13 (:REWRITE |(mod x 2)| . 2))
                        (11 11
                            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (11 11 (:REWRITE NORMALIZE-ADDENDS)))
(RP::DUMMY-ADDER-FINAL-STEP1
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (30 6 (:REWRITE RATIONALP-X))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::ADDER-SUM-OF-NIL)
(RP::ADDER-SUM-OF-NIL-2 (20 20 (:REWRITE DEFAULT-PLUS-2))
                        (20 20 (:REWRITE DEFAULT-PLUS-1))
                        (4 4 (:REWRITE REDUCE-INTEGERP-+))
                        (4 4 (:REWRITE INTEGERP-MINUS-X))
                        (4 4
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (4 4 (:META META-INTEGERP-CORRECT))
                        (2 2
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::SOME-COMBINATION-1
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::SOME-COMBINATION-1-SIDE-COND
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-M2
     (450 450
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (450 450
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (450 450
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (415 83 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (415 83 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (415 83
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (415 83
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (83 83 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (83 83
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (83 83 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (83 83 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (70 14 (:REWRITE RATIONALP-X))
     (56 4 (:REWRITE DEFAULT-MOD-RATIO))
     (56 2 (:LINEAR MOD-BOUNDS-3))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (30 6 (:REWRITE |(* y x)|))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (26 16 (:REWRITE DEFAULT-TIMES-2))
     (24 4 (:LINEAR MOD-BOUNDS-2))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (22 16 (:REWRITE DEFAULT-TIMES-1))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20 (:META META-INTEGERP-CORRECT))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (10 10
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 4 (:REWRITE DEFAULT-MOD-1))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE |(mod x 2)| . 2)))
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-F2
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-F2-SIDE-COND
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-M2-SIDE-COND
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIT-OF-ADDER-FNCS
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (12 8 (:REWRITE DEFAULT-TIMES-2))
     (12 8 (:REWRITE DEFAULT-TIMES-1))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
     (4 2 (:REWRITE O-INFP->NEQ-0))
     (4 2 (:REWRITE DEFAULT-FLOOR-1))
     (4 2 (:REWRITE |(* 1 x)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:META META-INTEGERP-CORRECT)))
(RP::ADDER-AND-OF-1 (57 2 (:REWRITE RP::BIT-FIX-OPENER))
                    (54 1 (:DEFINITION BITP))
                    (30 4
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (24 4 (:REWRITE ACL2-NUMBERP-X))
                    (10 4
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (10 2 (:REWRITE RATIONALP-X))
                    (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (4 4
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (4 4
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (4 4
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (4 4
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (4 4 (:REWRITE |(equal c (/ x))|))
                    (4 4 (:REWRITE |(equal c (- x))|))
                    (4 4 (:REWRITE |(equal (/ x) c)|))
                    (4 4 (:REWRITE |(equal (/ x) (/ y))|))
                    (4 4 (:REWRITE |(equal (- x) c)|))
                    (4 4 (:REWRITE |(equal (- x) (- y))|))
                    (2 2
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (2 2 (:REWRITE REDUCE-RATIONALP-+))
                    (2 2 (:REWRITE REDUCE-RATIONALP-*))
                    (2 2 (:REWRITE REDUCE-INTEGERP-+))
                    (2 2 (:REWRITE RATIONALP-MINUS-X))
                    (2 2
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (2 2 (:REWRITE INTEGERP-MINUS-X))
                    (2 2
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (2 2 (:META META-RATIONALP-CORRECT))
                    (2 2 (:META META-INTEGERP-CORRECT))
                    (2 1 (:REWRITE O-INFP->NEQ-0))
                    (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::ADDER-AND-OF-1-V2
     (57 2 (:REWRITE RP::BIT-FIX-OPENER))
     (54 1 (:DEFINITION BITP))
     (30 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 4 (:REWRITE ACL2-NUMBERP-X))
     (10 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 2 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::ADDER-AND-OF-0 (56 1 (:REWRITE RP::BIT-FIX-OPENER))
                    (54 1 (:DEFINITION BITP))
                    (28 3
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (24 4 (:REWRITE ACL2-NUMBERP-X))
                    (10 2 (:REWRITE RATIONALP-X))
                    (8 3
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (4 4
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                    (2 2 (:REWRITE REDUCE-RATIONALP-+))
                    (2 2 (:REWRITE REDUCE-RATIONALP-*))
                    (2 2 (:REWRITE REDUCE-INTEGERP-+))
                    (2 2 (:REWRITE RATIONALP-MINUS-X))
                    (2 2
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (2 2 (:REWRITE INTEGERP-MINUS-X))
                    (2 2
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (2 2 (:META META-RATIONALP-CORRECT))
                    (2 2 (:META META-INTEGERP-CORRECT))
                    (1 1 (:TYPE-PRESCRIPTION BITP))
                    (1 1
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::ADDER-AND-OF-0-V2)
(RP::ADDER-OR-OF-0 (57 2 (:REWRITE RP::BIT-FIX-OPENER))
                   (54 1 (:DEFINITION BITP))
                   (28 3
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (24 4 (:REWRITE ACL2-NUMBERP-X))
                   (10 2 (:REWRITE RATIONALP-X))
                   (8 3
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (4 4
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                   (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                   (2 2
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (2 2 (:REWRITE REDUCE-RATIONALP-+))
                   (2 2 (:REWRITE REDUCE-RATIONALP-*))
                   (2 2 (:REWRITE REDUCE-INTEGERP-+))
                   (2 2 (:REWRITE RATIONALP-MINUS-X))
                   (2 2
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (2 2 (:REWRITE INTEGERP-MINUS-X))
                   (2 2
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (2 2 (:META META-RATIONALP-CORRECT))
                   (2 2 (:META META-INTEGERP-CORRECT))
                   (2 1 (:REWRITE O-INFP->NEQ-0))
                   (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::ADDER-OR-OF-0-V2
     (57 2 (:REWRITE RP::BIT-FIX-OPENER))
     (54 1 (:DEFINITION BITP))
     (28 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 4 (:REWRITE ACL2-NUMBERP-X))
     (10 2 (:REWRITE RATIONALP-X))
     (8 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::ADDER-OR-OF-1 (56 1 (:REWRITE RP::BIT-FIX-OPENER))
                   (54 1 (:DEFINITION BITP))
                   (28 3
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (24 4 (:REWRITE ACL2-NUMBERP-X))
                   (10 2 (:REWRITE RATIONALP-X))
                   (8 3
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (4 4
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                   (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                   (2 2
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (2 2 (:REWRITE REDUCE-RATIONALP-+))
                   (2 2 (:REWRITE REDUCE-RATIONALP-*))
                   (2 2 (:REWRITE REDUCE-INTEGERP-+))
                   (2 2 (:REWRITE RATIONALP-MINUS-X))
                   (2 2
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (2 2 (:REWRITE INTEGERP-MINUS-X))
                   (2 2
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (2 2 (:META META-RATIONALP-CORRECT))
                   (2 2 (:META META-INTEGERP-CORRECT))
                   (2 1 (:REWRITE O-INFP->NEQ-0))
                   (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::ADDER-OR-OF-1-V2)
(RP::ADDER-OR-OF-THE-SAME
     (111 3 (:REWRITE RP::BIT-FIX-OPENER))
     (106 2 (:DEFINITION BITP))
     (47 7 (:REWRITE ACL2-NUMBERP-X))
     (42 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (20 4 (:REWRITE RATIONALP-X))
     (7 7
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::ADDER-AND-OF-THE-SAME
     (111 3 (:REWRITE RP::BIT-FIX-OPENER))
     (106 2 (:DEFINITION BITP))
     (47 7 (:REWRITE ACL2-NUMBERP-X))
     (44 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (20 4 (:REWRITE RATIONALP-X))
     (7 7
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
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
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::BITP-OF-BINARY-FNCS)
