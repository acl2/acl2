(RP::AND$-IS-ADDER-AND$)
(RP::OR$-IS-ADDER-OR$)
(RP::SUM-IS-ADDER-B+)
(RP::PP-SUM-IS-ADDER-B+)
(RP::MERGE-PP-SUM-IS-ADDER-B+)
(RP::MERGE-SUM-IS-ADDER-B+)
(RP::PP-SUM-IS-ADDER-B+-2)
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
(RP::MERGE-ADDER-SUM-IS-ADDER-SUM)
(RP::BIN-XOR-IS-S (145 29
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                  (140 140
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (140 140
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (140 28 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                  (78 6
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (72 12 (:REWRITE ACL2-NUMBERP-X))
                  (56 4 (:REWRITE DEFAULT-MOD-RATIO))
                  (56 2 (:LINEAR MOD-BOUNDS-3))
                  (30 6 (:REWRITE RATIONALP-X))
                  (30 6 (:REWRITE |(* y x)|))
                  (29 29
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                  (28 28 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                  (28 28 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                  (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                  (27 27
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                  (26 16 (:REWRITE DEFAULT-TIMES-2))
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
(RP::BIN-XOR-IS-S-SC (240 48
                          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                     (230 46 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                     (218 218
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (218 218
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (78 6
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (72 12 (:REWRITE ACL2-NUMBERP-X))
                     (48 48
                         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                     (46 46 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                     (46 46 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                     (40 40 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                     (40 40
                         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                     (30 6 (:REWRITE RATIONALP-X))
                     (28 2 (:REWRITE DEFAULT-MOD-RATIO))
                     (28 1 (:LINEAR MOD-BOUNDS-3))
                     (18 6
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (18 3 (:REWRITE O-INFP->NEQ-0))
                     (15 3 (:REWRITE |(* y x)|))
                     (13 8 (:REWRITE DEFAULT-TIMES-2))
                     (12 12
                         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (12 2 (:LINEAR MOD-BOUNDS-2))
                     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (11 8 (:REWRITE DEFAULT-TIMES-1))
                     (9 9 (:TYPE-PRESCRIPTION O-FINP))
                     (9 9 (:REWRITE REDUCE-INTEGERP-+))
                     (9 9 (:REWRITE INTEGERP-MINUS-X))
                     (9 9
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (9 9 (:META META-INTEGERP-CORRECT))
                     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
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
                     (5 5
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (4 2 (:REWRITE DEFAULT-MOD-1))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                     (2 2 (:REWRITE DEFAULT-MOD-2))
                     (2 2 (:REWRITE |(mod x 2)| . 2)))
(RP::BIN-AND-IS-C (637 637
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (637 637
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (261 29
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (261 29
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (238 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (234 26
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (225 25
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (145 29
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (145 29
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (145 29
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (145 29
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (130 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (130 26
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (130 26
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (130 26
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::BIN-AND-IS-C-3 (679 679
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (679 679
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (261 29
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                    (261 29
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                    (238 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                    (234 26
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                    (225 25
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                    (193 21
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (168 28 (:REWRITE ACL2-NUMBERP-X))
                    (145 29
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                    (145 29
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                    (145 29
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                    (145 29
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                    (130 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                    (130 26
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                    (130 26
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                    (130 26
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                    (70 14 (:REWRITE RATIONALP-X))
                    (53 21
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (28 28
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (21 21
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (21 21
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (21 21
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (21 21 (:REWRITE |(equal c (/ x))|))
                    (21 21 (:REWRITE |(equal c (- x))|))
                    (21 21 (:REWRITE |(equal (/ x) c)|))
                    (21 21 (:REWRITE |(equal (/ x) (/ y))|))
                    (21 21 (:REWRITE |(equal (- x) c)|))
                    (21 21 (:REWRITE |(equal (- x) (- y))|))
                    (18 3 (:REWRITE O-INFP->NEQ-0))
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
                    (9 9 (:TYPE-PRESCRIPTION O-FINP))
                    (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                    (7 7
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::BIN-AND-IS-C-3-SIDE-COND
     (737 737
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (737 737
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (315 35
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (315 35
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (277 29 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (261 29
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (175 35
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (175 35
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (175 35
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (175 35
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (145 29 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (145 29
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (145 29
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (145 29
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (132 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (120 72 (:REWRITE DEFAULT-TIMES-2))
     (112 8 (:REWRITE DEFAULT-FLOOR-RATIO))
     (112 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (96 72 (:REWRITE DEFAULT-TIMES-1))
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (48 48
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (36 16 (:REWRITE DEFAULT-PLUS-2))
     (36 16 (:REWRITE DEFAULT-PLUS-1))
     (30 6 (:REWRITE RATIONALP-X))
     (22 22 (:REWRITE REDUCE-INTEGERP-+))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (22 22
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (22 22 (:META META-INTEGERP-CORRECT))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (16 8 (:REWRITE DEFAULT-FLOOR-1))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (8 8 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE |(floor x 2)| . 2))
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
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BIN-AND-IS-C-SC (737 737
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (737 737
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (315 35
                          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                     (315 35
                          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                     (277 29 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                     (261 29
                          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                     (225 25
                          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                     (175 35
                          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                     (175 35
                          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                     (175 35
                          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                     (175 35
                          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                     (145 29 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                     (145 29
                          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                     (145 29
                          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                     (145 29
                          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                     (132 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                     (120 72 (:REWRITE DEFAULT-TIMES-2))
                     (112 8 (:REWRITE DEFAULT-FLOOR-RATIO))
                     (112 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                     (96 72 (:REWRITE DEFAULT-TIMES-1))
                     (78 6
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (72 12 (:REWRITE ACL2-NUMBERP-X))
                     (48 48
                         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (36 16 (:REWRITE DEFAULT-PLUS-2))
                     (36 16 (:REWRITE DEFAULT-PLUS-1))
                     (30 6 (:REWRITE RATIONALP-X))
                     (22 22 (:REWRITE REDUCE-INTEGERP-+))
                     (22 22 (:REWRITE INTEGERP-MINUS-X))
                     (22 22
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (22 22 (:META META-INTEGERP-CORRECT))
                     (18 6
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (18 3 (:REWRITE O-INFP->NEQ-0))
                     (16 8 (:REWRITE DEFAULT-FLOOR-1))
                     (12 12
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (12 12 (:REWRITE NORMALIZE-ADDENDS))
                     (12 12
                         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (9 9 (:TYPE-PRESCRIPTION O-FINP))
                     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                     (8 8 (:REWRITE DEFAULT-FLOOR-2))
                     (8 8 (:REWRITE |(floor x 2)| . 2))
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
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::C-OF-SAME-C)
(RP::BIN-OR-P1 (939 939
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (939 939
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (369 41
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (369 41
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (349 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (333 37
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
               (297 33
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
               (205 41
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
               (205 41
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (205 41
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
               (205 41
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (185 37
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
               (185 37
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
               (185 37
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
               (182 14
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (168 28 (:REWRITE ACL2-NUMBERP-X))
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
(RP::BIN-OR-P1A (939 939
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (939 939
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (369 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (369 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (349 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (333 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (182 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (168 28 (:REWRITE ACL2-NUMBERP-X))
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
(RP::BIN-OR-P1B (887 887
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (887 887
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (369 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (369 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (349 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (333 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (182 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (168 28 (:REWRITE ACL2-NUMBERP-X))
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
(RP::BIN-OR-P1B-V2
     (1882 1882
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1882 1882
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (874 82 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (774 86
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (774 86
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (738 82
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (628 50
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (576 96 (:REWRITE ACL2-NUMBERP-X))
     (432 48
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (410 82 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (410 82
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (410 82
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (410 82
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (240 48 (:REWRITE RATIONALP-X))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (148 50
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (144 24 (:REWRITE O-INFP->NEQ-0))
     (107 5 (:REWRITE DEFAULT-FLOOR-RATIO))
     (100 67 (:REWRITE REDUCE-INTEGERP-+))
     (100 67 (:META META-INTEGERP-CORRECT))
     (96 96
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (86 22 (:REWRITE DEFAULT-PLUS-2))
     (72 72 (:TYPE-PRESCRIPTION O-FINP))
     (72 24 (:REWRITE O-FIRST-EXPT-O-INFP))
     (70 22 (:REWRITE DEFAULT-PLUS-1))
     (68 68 (:REWRITE DEFAULT-TIMES-2))
     (68 68 (:REWRITE DEFAULT-TIMES-1))
     (67 67 (:REWRITE INTEGERP-MINUS-X))
     (67 67
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (54 54
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (54 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (52 50 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (50 50 (:REWRITE |(equal c (/ x))|))
     (50 50 (:REWRITE |(equal c (- x))|))
     (50 50 (:REWRITE |(equal (/ x) c)|))
     (50 50 (:REWRITE |(equal (/ x) (/ y))|))
     (50 50 (:REWRITE |(equal (- x) c)|))
     (50 50 (:REWRITE |(equal (- x) (- y))|))
     (48 48 (:REWRITE REDUCE-RATIONALP-+))
     (48 48 (:REWRITE REDUCE-RATIONALP-*))
     (48 48 (:REWRITE RATIONALP-MINUS-X))
     (48 48
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (48 48 (:META META-RATIONALP-CORRECT))
     (48 24 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (46 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (34 1 (:REWRITE DEFAULT-MOD-RATIO))
     (28 1 (:REWRITE |(floor (+ x r) i)|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 1 (:REWRITE SUM-IS-EVEN . 2))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE DEFAULT-FLOOR-1))
     (5 5 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(mod x 2)| . 2))
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
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::BIN-OR-P1B-V3
     (1882 1882
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1882 1882
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (874 82 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (774 86
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (774 86
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (738 82
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (628 50
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (576 96 (:REWRITE ACL2-NUMBERP-X))
     (432 48
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (430 86
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (410 82 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (410 82
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (410 82
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (410 82
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (240 48 (:REWRITE RATIONALP-X))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (148 50
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (144 24 (:REWRITE O-INFP->NEQ-0))
     (107 5 (:REWRITE DEFAULT-FLOOR-RATIO))
     (100 67 (:REWRITE REDUCE-INTEGERP-+))
     (100 67 (:META META-INTEGERP-CORRECT))
     (96 96
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (86 22 (:REWRITE DEFAULT-PLUS-2))
     (72 72 (:TYPE-PRESCRIPTION O-FINP))
     (72 24 (:REWRITE O-FIRST-EXPT-O-INFP))
     (70 22 (:REWRITE DEFAULT-PLUS-1))
     (68 68 (:REWRITE DEFAULT-TIMES-2))
     (68 68 (:REWRITE DEFAULT-TIMES-1))
     (67 67 (:REWRITE INTEGERP-MINUS-X))
     (67 67
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (54 54
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (54 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (52 50 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (50 50 (:REWRITE |(equal c (/ x))|))
     (50 50 (:REWRITE |(equal c (- x))|))
     (50 50 (:REWRITE |(equal (/ x) c)|))
     (50 50 (:REWRITE |(equal (/ x) (/ y))|))
     (50 50 (:REWRITE |(equal (- x) c)|))
     (50 50 (:REWRITE |(equal (- x) (- y))|))
     (48 48 (:REWRITE REDUCE-RATIONALP-+))
     (48 48 (:REWRITE REDUCE-RATIONALP-*))
     (48 48 (:REWRITE RATIONALP-MINUS-X))
     (48 48
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (48 48 (:META META-RATIONALP-CORRECT))
     (48 24 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (46 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (34 1 (:REWRITE DEFAULT-MOD-RATIO))
     (28 1 (:REWRITE |(floor (+ x r) i)|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 1 (:REWRITE SUM-IS-EVEN . 2))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE DEFAULT-FLOOR-1))
     (5 5 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(mod x 2)| . 2))
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
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::BIN-OR-P1C (939 939
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (939 939
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (369 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (369 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (349 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (333 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (297 33
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (205 41
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (185 37
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (182 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (168 28 (:REWRITE ACL2-NUMBERP-X))
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
(RP::BIN-OR-P2A (1415 1415
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1415 1415
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (585 65
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (585 65
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (571 59 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (531 59
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (390 30
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (360 60 (:REWRITE ACL2-NUMBERP-X))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (295 59 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (295 59
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (295 59
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (295 59
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::BIN-OR-P2B (2327 2327
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (2327 2327
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (1017 113
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (1017 113
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (963 99 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (891 99
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (806 62
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (744 124 (:REWRITE ACL2-NUMBERP-X))
                (729 81
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (565 113
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (565 113
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (565 113
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (565 113
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (495 99 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (495 99
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (495 99
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (495 99
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::BIN-OR-P2C (1415 1415
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1415 1415
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (585 65
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (585 65
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (571 59 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (531 59
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (441 49
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (390 30
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (360 60 (:REWRITE ACL2-NUMBERP-X))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (325 65
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (295 59 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (295 59
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (295 59
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (295 59
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::BIN-OR-P3 (2890 2890
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (2890 2890
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (1170 130
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (1170 130
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (1130 122 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (1098 122
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
               (1026 114
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
               (738 78
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (650 130
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
               (650 130
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (650 130
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
               (650 130
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (648 108 (:REWRITE ACL2-NUMBERP-X))
               (610 122 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (610 122
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
               (610 122
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
               (610 122
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::BIN-OR-P2-SC (2273 2273
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (2273 2273
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (1069 101 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (1017 113
                        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (1017 113
                        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (909 101
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (565 113
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (565 113
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (565 113
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (565 113
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (549 61
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (505 101 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (505 101
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (505 101
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (505 101
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (390 30
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (360 60 (:REWRITE ACL2-NUMBERP-X))
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
     (4081 4081
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4081 4081
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1917 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1881 209
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1881 209
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1629 181
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (1045 209
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1045 209
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1045 209
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (1045 209
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (981 109
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (905 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (905 181
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (905 181
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (905 181
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (806 62
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (744 124 (:REWRITE ACL2-NUMBERP-X))
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
(RP::BIN-OR-P1-SC (1249 1249
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (1249 1249
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (549 61
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (549 61
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (541 53 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (477 53
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (333 37
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (305 61
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (305 61
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (305 61
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (305 61
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (265 53 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (265 53
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (265 53
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (265 53
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::ADDER-SUM-OF-PP-SUM
     (99 99 (:REWRITE DEFAULT-PLUS-2))
     (99 99 (:REWRITE DEFAULT-PLUS-1))
     (19 19
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (19 19 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(+ c (+ d x))|)))
(RP::PP-SUM-OF-ADDER-SUM
     (99 99 (:REWRITE DEFAULT-PLUS-2))
     (99 99 (:REWRITE DEFAULT-PLUS-1))
     (19 19
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (19 19 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(+ c (+ d x))|)))
(RP::ADDER-SUM-OF-0 (5 5 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::ADDER-TYPE-FIX)
(RP::M2-OF-ADDER-SUM-M2 (902 22 (:REWRITE DEFAULT-MOD-RATIO))
                        (625 125 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                        (625 125 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                        (625 125
                             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                        (625 125
                             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                        (611 611
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (611 611
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (611 611
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                        (397 31 (:REWRITE |(* y x)|))
                        (394 110 (:REWRITE DEFAULT-TIMES-2))
                        (349 3 (:LINEAR MOD-BOUNDS-3))
                        (326 110 (:REWRITE DEFAULT-TIMES-1))
                        (245 17 (:REWRITE |(* (if a b c) x)|))
                        (181 181
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                        (181 181
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                        (181 181
                             (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                        (158 22 (:REWRITE DEFAULT-MOD-1))
                        (142 6 (:LINEAR MOD-BOUNDS-2))
                        (125 125 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                        (125 125
                             (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                        (125 125
                             (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                        (125 125
                             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                        (125 125 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                        (61 61
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (60 24 (:REWRITE DEFAULT-PLUS-2))
                        (60 24 (:REWRITE DEFAULT-PLUS-1))
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
     (883 883
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (883 883
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (288 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (288 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (265 29 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (261 29
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (252 28
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (145 29 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (145 29
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (145 29
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (145 29
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (100 20
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (100 20
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (85 17 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (30 6 (:REWRITE RATIONALP-X))
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (20 20
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (20 20
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (17 17 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (17 17 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
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
(RP::ADDER-SUM-OF-NIL (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
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
     (875 875
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (875 875
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (369 41
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (369 41
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (349 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (333 37
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (297 33
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (205 41
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (205 41
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (205 41
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (205 41
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (185 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (185 37
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (185 37
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (185 37
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
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
(RP::SOME-COMBINATION-1-SIDE-COND
     (1249 1249
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1249 1249
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (549 61
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (549 61
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (541 53 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (477 53
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (333 37
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (265 53 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (265 53
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (265 53
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (265 53
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-M2
     (675 675
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (675 675
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (615 123
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (590 118 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (123 123
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (118 118
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (118 118 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (108 108 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (108 108
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (70 14 (:REWRITE RATIONALP-X))
     (46 2 (:LINEAR MOD-BOUNDS-3))
     (44 4 (:REWRITE DEFAULT-MOD-RATIO))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (24 6 (:REWRITE |(* y x)|))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20 (:META META-INTEGERP-CORRECT))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (16 16 (:REWRITE DEFAULT-TIMES-2))
     (16 16 (:REWRITE DEFAULT-TIMES-1))
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
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE |(mod x 2)| . 2)))
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-F2
     (2836 2836
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2836 2836
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1235 103 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1107 123
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1107 123
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (927 103
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (615 123
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (615 123
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (615 123
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (615 123
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (515 103 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (515 103
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (515 103
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (515 103
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (234 26
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (70 14 (:REWRITE RATIONALP-X))
     (54 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (46 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (44 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (36 36 (:REWRITE DEFAULT-TIMES-2))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
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
     (16 8 (:REWRITE DEFAULT-PLUS-2))
     (16 8 (:REWRITE DEFAULT-PLUS-1))
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
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (4 4 (:REWRITE |(floor x 2)| . 2)))
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-F2-SIDE-COND
     (1249 1249
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1249 1249
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (549 61
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (549 61
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (541 53 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (477 53
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (333 37
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (305 61
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (265 53 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (265 53
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (265 53
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (265 53
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
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
(RP::ADDER-OR-OF-AND-AND-NOTS-WITH-M2-SIDE-COND
     (430 86
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (420 84 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (384 384
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (384 384
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (182 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (86 86
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (84 84 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (84 84 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (74 74 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (74 74
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (70 14 (:REWRITE RATIONALP-X))
     (42 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 7 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (28 2 (:REWRITE DEFAULT-MOD-RATIO))
     (28 1 (:LINEAR MOD-BOUNDS-3))
     (21 21 (:TYPE-PRESCRIPTION O-FINP))
     (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
     (17 17 (:REWRITE REDUCE-INTEGERP-+))
     (17 17 (:REWRITE INTEGERP-MINUS-X))
     (17 17
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (17 17 (:META META-INTEGERP-CORRECT))
     (15 3 (:REWRITE |(* y x)|))
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
     (13 8 (:REWRITE DEFAULT-TIMES-2))
     (12 2 (:LINEAR MOD-BOUNDS-2))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (11 8 (:REWRITE DEFAULT-TIMES-1))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2)))
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
