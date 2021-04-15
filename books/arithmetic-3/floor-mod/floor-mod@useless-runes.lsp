(RATIONALP-GUARD-FN (222 12 (:DEFINITION INTEGER-ABS))
                    (179 61 (:REWRITE DEFAULT-+-2))
                    (114 6 (:REWRITE |(+ (if a b c) x)|))
                    (82 61 (:REWRITE DEFAULT-+-1))
                    (66 6 (:REWRITE NUMERATOR-NEGATIVE))
                    (61 61
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (60 6 (:DEFINITION LENGTH))
                    (42 26
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                    (42 6 (:DEFINITION LEN))
                    (40 14 (:REWRITE DEFAULT-UNARY-MINUS))
                    (33 19
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                    (33 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                    (30 30 (:REWRITE DEFAULT-CDR))
                    (26 26
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                    (25 25 (:REWRITE |(< (- x) (- y))|))
                    (24 24
                        (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                    (24 24
                        (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                    (24 24
                        (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                    (24 24
                        (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                    (24 18 (:REWRITE DEFAULT-<-2))
                    (23 23 (:REWRITE |(+ c (+ d x))|))
                    (23 18 (:REWRITE DEFAULT-<-1))
                    (21 21 (:REWRITE FOLD-CONSTS-IN-+))
                    (18 18 (:REWRITE |(< (- x) 0)|))
                    (14 14 (:REWRITE DEFAULT-CAR))
                    (12 12
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                    (6 6 (:TYPE-PRESCRIPTION LEN))
                    (6 6 (:REWRITE REDUCE-INTEGERP-+))
                    (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                    (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                    (6 6 (:REWRITE INTEGERP-MINUS-X))
                    (6 6 (:REWRITE DEFAULT-REALPART))
                    (6 6 (:REWRITE DEFAULT-NUMERATOR))
                    (6 6 (:REWRITE DEFAULT-IMAGPART))
                    (6 6 (:REWRITE DEFAULT-DENOMINATOR))
                    (6 6 (:REWRITE DEFAULT-COERCE-2))
                    (6 6 (:REWRITE DEFAULT-COERCE-1))
                    (6 6 (:META META-INTEGERP-CORRECT))
                    (2 1 (:REWRITE |(< d (+ c x y))|)))
(NIQ-BOUNDS (624 624
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (624 624
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (624 624
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (166 85
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (151 81 (:REWRITE SIMPLIFY-SUMS-<))
            (137 81 (:REWRITE DEFAULT-<-1))
            (130 90
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
            (95 81 (:REWRITE DEFAULT-<-2))
            (86 86 (:REWRITE |(< (- x) (- y))|))
            (73 41 (:REWRITE DEFAULT-+-2))
            (41 41
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (41 41 (:REWRITE DEFAULT-+-1))
            (32 32 (:REWRITE |(< (- x) 0)|))
            (30 30
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
            (26 26 (:REWRITE REDUCE-INTEGERP-+))
            (26 26 (:REWRITE INTEGERP-MINUS-X))
            (26 26 (:META META-INTEGERP-CORRECT))
            (18 18
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (18 18
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (18 18 (:REWRITE DEFAULT-UNARY-/))
            (18 18 (:REWRITE DEFAULT-*-2))
            (18 18 (:REWRITE DEFAULT-*-1))
            (18 10 (:REWRITE |(< d (+ c x))|))
            (15 15
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
            (15 15 (:REWRITE |(< 0 (- x))|))
            (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
            (12 12 (:REWRITE |arith (* c (* d x))|))
            (6 6 (:REWRITE |arith (- (* c x))|))
            (6 6 (:REWRITE |arith (* (- x) y)|))
            (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
            (2 1 (:REWRITE |(< (+ d x) (+ c y))|))
            (1 1
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
            (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (1 1
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (1 1
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (1 1 (:REWRITE |(equal (- x) 0)|))
            (1 1 (:REWRITE |(equal (- x) (- y))|)))
(TRUNCATE-TO-FLOOR (116 116
                        (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                   (116 116
                        (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                   (116 116
                        (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                   (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                   (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (39 9 (:REWRITE DEFAULT-UNARY-/))
                   (31 31
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (31 31
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (27 27 (:REWRITE |(< (- x) (- y))|))
                   (23 13
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (23 13
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (20 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                   (18 6 (:REWRITE DEFAULT-UNARY-MINUS))
                   (17 17 (:REWRITE SIMPLIFY-SUMS-<))
                   (17 17
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (17 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (17 17 (:REWRITE DEFAULT-<-2))
                   (17 17 (:REWRITE DEFAULT-<-1))
                   (16 16 (:REWRITE |(equal (- x) (- y))|))
                   (16 16 (:REWRITE |(< (- x) 0)|))
                   (11 11 (:REWRITE |(equal (- x) 0)|))
                   (11 11 (:REWRITE |(< 0 (- x))|))
                   (9 9
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                   (9 9
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                   (9 9
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                   (9 9
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (9 9 (:REWRITE DEFAULT-*-2))
                   (9 9 (:REWRITE DEFAULT-*-1))
                   (8 8
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                   (8 4 (:REWRITE DEFAULT-NUMERATOR))
                   (8 4 (:REWRITE DEFAULT-DENOMINATOR))
                   (6 6 (:REWRITE REDUCE-INTEGERP-+))
                   (6 6 (:REWRITE INTEGERP-MINUS-X))
                   (6 6 (:REWRITE |(integerp (* c x))|))
                   (6 6 (:META META-INTEGERP-CORRECT))
                   (4 2 (:REWRITE DEFAULT-+-2))
                   (2 2
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (2 2 (:REWRITE DEFAULT-+-1))
                   (2 1 (:REWRITE |(equal (+ c x) d)|)))
(REM-TO-MOD (512 8
                 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
            (88 8 (:DEFINITION NFIX))
            (74 42 (:REWRITE SIMPLIFY-SUMS-<))
            (74 42
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (74 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
            (74 42 (:REWRITE DEFAULT-<-1))
            (66 66
                (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
            (66 66
                (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
            (66 66
                (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
            (66 66
                (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
            (62 62
                (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
            (62 62
                (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
            (62 35 (:REWRITE DEFAULT-+-2))
            (56 56 (:REWRITE |(< (- x) (- y))|))
            (42 42 (:REWRITE DEFAULT-<-2))
            (42 24 (:REWRITE DEFAULT-UNARY-MINUS))
            (40 8 (:DEFINITION IFIX))
            (39 9 (:REWRITE DEFAULT-UNARY-/))
            (35 35
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (35 35 (:REWRITE DEFAULT-+-1))
            (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (32 32 (:REWRITE |(< (- x) 0)|))
            (25 17 (:REWRITE DEFAULT-*-2))
            (22 22
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
            (17 17
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (17 17 (:REWRITE DEFAULT-*-1))
            (16 16 (:REWRITE |(< 0 (- x))|))
            (13 13 (:REWRITE |(equal (- x) 0)|))
            (13 13 (:REWRITE |(equal (- x) (- y))|))
            (12 12
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
            (11 11
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
            (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (11 11
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (11 11
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (9 9
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (8 8 (:REWRITE |(- (* c x))|))
            (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
            (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
            (6 6 (:REWRITE DEFAULT-NUMERATOR))
            (6 6 (:REWRITE DEFAULT-DENOMINATOR))
            (3 3 (:REWRITE FOLD-CONSTS-IN-+))
            (2 2 (:REWRITE REDUCE-INTEGERP-+))
            (2 2 (:REWRITE INTEGERP-MINUS-X))
            (2 2 (:REWRITE |(integerp (* c x))|))
            (2 2 (:META META-INTEGERP-CORRECT)))
(CEILING-TO-FLOOR (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                  (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (68 68
                      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                  (68 68
                      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                  (68 68
                      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                  (37 7 (:REWRITE DEFAULT-UNARY-/))
                  (18 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                  (16 16
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                  (16 16
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                  (14 14 (:REWRITE |(< (- x) (- y))|))
                  (14 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (14 10
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (14 10
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (14 4 (:REWRITE DEFAULT-UNARY-MINUS))
                  (13 13 (:REWRITE |(equal (- x) (- y))|))
                  (11 11 (:REWRITE |(equal (- x) 0)|))
                  (9 9
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                  (8 8 (:REWRITE SIMPLIFY-SUMS-<))
                  (8 8
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                  (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                  (8 8 (:REWRITE DEFAULT-<-2))
                  (8 8 (:REWRITE DEFAULT-<-1))
                  (8 8 (:REWRITE |(< (- x) 0)|))
                  (7 7
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                  (7 7
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (7 7 (:REWRITE DEFAULT-*-2))
                  (7 7 (:REWRITE DEFAULT-*-1))
                  (6 6 (:REWRITE REDUCE-INTEGERP-+))
                  (6 6 (:REWRITE INTEGERP-MINUS-X))
                  (6 6 (:REWRITE |(integerp (* c x))|))
                  (6 6 (:REWRITE |(< 0 (- x))|))
                  (6 6 (:META META-INTEGERP-CORRECT))
                  (6 3 (:REWRITE DEFAULT-+-2))
                  (6 2 (:REWRITE DEFAULT-NUMERATOR))
                  (6 2 (:REWRITE DEFAULT-DENOMINATOR))
                  (4 4
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                  (4 4
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                  (3 3
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (3 3 (:REWRITE NORMALIZE-ADDENDS))
                  (3 3 (:REWRITE DEFAULT-+-1)))
(ROUND-TO-FLOOR (623 623
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (623 623
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (623 623
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (554 554
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (554 554
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (291 291
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (291 291
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (291 291
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (252 57 (:REWRITE DEFAULT-UNARY-MINUS))
                (218 71 (:REWRITE DEFAULT-+-2))
                (208 62 (:REWRITE DEFAULT-UNARY-/))
                (145 80 (:REWRITE DEFAULT-*-2))
                (131 19
                     (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                (121 117
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (117 117
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (102 72
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (101 101 (:REWRITE |(< (- x) (- y))|))
                (96 80 (:REWRITE DEFAULT-*-1))
                (80 80
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (72 48
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (71 71
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (71 71 (:REWRITE DEFAULT-+-1))
                (66 58 (:REWRITE DEFAULT-<-2))
                (65 58 (:REWRITE DEFAULT-<-1))
                (63 51 (:META META-INTEGERP-CORRECT))
                (62 62
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (47 47 (:REWRITE |(equal (- x) 0)|))
                (47 19 (:REWRITE DEFAULT-NUMERATOR))
                (47 19 (:REWRITE DEFAULT-DENOMINATOR))
                (46 46 (:REWRITE |(< (- x) 0)|))
                (44 44 (:REWRITE REDUCE-INTEGERP-+))
                (43 43 (:REWRITE |(integerp (* c x))|))
                (38 38
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (35 35 (:REWRITE |(< 0 (- x))|))
                (27 27
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (25 25
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (25 15 (:REWRITE |(< d (+ c x))|))
                (23 13 (:REWRITE |(< (+ c x) d)|))
                (22 9 (:REWRITE |(equal (+ c x) d)|))
                (15 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
                (15 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                (15 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                (15 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                (12 12 (:REWRITE FOLD-CONSTS-IN-+))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
                (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C)))
(ASH-TO-FLOOR (262 262
                   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
              (105 21 (:REWRITE DEFAULT-*-2))
              (57 9 (:REWRITE DEFAULT-+-2))
              (56 10 (:REWRITE DEFAULT-UNARY-MINUS))
              (54 8
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (44 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (40 20 (:REWRITE SIMPLIFY-SUMS-<))
              (40 20
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
              (38 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (35 27
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
              (32 20 (:REWRITE DEFAULT-<-2))
              (32 20 (:REWRITE DEFAULT-<-1))
              (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (23 23 (:REWRITE |(< (- x) (- y))|))
              (21 21 (:REWRITE REDUCE-INTEGERP-+))
              (21 21
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (21 21 (:REWRITE INTEGERP-MINUS-X))
              (21 21 (:REWRITE DEFAULT-*-1))
              (21 21 (:META META-INTEGERP-CORRECT))
              (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (20 17 (:REWRITE |(expt 2^i n)|))
              (20 2 (:LINEAR EXPT->-1-ONE))
              (20 2 (:LINEAR EXPT-<-1-TWO))
              (17 17 (:REWRITE |(expt 1/c n)|))
              (17 17 (:REWRITE |(expt (- x) n)|))
              (17 9 (:REWRITE DEFAULT-UNARY-/))
              (17 3 (:REWRITE |(equal (+ c x) d)|))
              (16 2 (:LINEAR EXPT-X->=-X))
              (16 2 (:LINEAR EXPT-X->-X))
              (15 15 (:REWRITE DEFAULT-EXPT-1))
              (15 9 (:REWRITE DEFAULT-+-1))
              (12 12 (:REWRITE |(< (- x) 0)|))
              (9 9
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (9 9
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (9 9
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (9 9 (:REWRITE |(equal (- x) (- y))|))
              (9 5 (:REWRITE DEFAULT-NUMERATOR))
              (9 5 (:REWRITE DEFAULT-DENOMINATOR))
              (7 7
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (7 7 (:REWRITE |(integerp (* c x))|))
              (7 7 (:REWRITE |(< 0 (- x))|))
              (7 1 (:REWRITE |(equal (+ c x y) d)|))
              (4 4 (:REWRITE |(- (* c x))|))
              (4 4
                 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
              (4 4
                 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
              (4 4
                 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
              (4 4
                 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
              (3 3
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (3 3 (:REWRITE |(equal (- x) 0)|))
              (2 2 (:LINEAR EXPT->-1-TWO))
              (2 2 (:LINEAR EXPT-<-1-ONE))
              (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(INTEGERP-MOD (128 2
                   (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
              (22 2 (:DEFINITION NFIX))
              (21 21
                  (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
              (21 21
                  (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
              (21 21
                  (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
              (21 21
                  (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
              (21 10 (:REWRITE DEFAULT-+-2))
              (19 8 (:REWRITE DEFAULT-UNARY-MINUS))
              (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (17 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
              (17 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
              (16 8 (:REWRITE SIMPLIFY-SUMS-<))
              (16 8
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
              (16 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (16 8 (:REWRITE DEFAULT-<-1))
              (12 12
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
              (12 12
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
              (11 11 (:REWRITE |(< (- x) (- y))|))
              (10 10
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (10 10 (:REWRITE NORMALIZE-ADDENDS))
              (10 10 (:REWRITE DEFAULT-+-1))
              (10 4 (:REWRITE DEFAULT-*-2))
              (10 2 (:DEFINITION IFIX))
              (8 8 (:REWRITE DEFAULT-<-2))
              (7 1 (:REWRITE DEFAULT-UNARY-/))
              (6 6 (:REWRITE REDUCE-INTEGERP-+))
              (6 6 (:REWRITE INTEGERP-MINUS-X))
              (6 6 (:REWRITE |(< (- x) 0)|))
              (6 6 (:META META-INTEGERP-CORRECT))
              (5 5 (:REWRITE |(equal (- x) (- y))|))
              (5 1 (:REWRITE DEFAULT-NUMERATOR))
              (5 1 (:REWRITE DEFAULT-DENOMINATOR))
              (4 4
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (4 4
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (4 4 (:REWRITE DEFAULT-*-1))
              (4 4 (:REWRITE |(integerp (* c x))|))
              (4 4 (:REWRITE |(equal (- x) 0)|))
              (3 3
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (3 3
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (3 3
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (3 3 (:REWRITE |(< 0 (- x))|))
              (3 3 (:REWRITE |(- (* c x))|))
              (2 2
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (1 1
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (1 1 (:REWRITE FOLD-CONSTS-IN-+))
              (1 1 (:REWRITE |(+ c (+ d x))|)))
(RATIONALP-MOD (128 2
                    (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
               (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
               (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (46 11 (:REWRITE DEFAULT-+-2))
               (44 9 (:REWRITE DEFAULT-UNARY-MINUS))
               (41 25
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
               (41 25
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
               (41 25
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
               (38 38 (:TYPE-PRESCRIPTION INTEGERP-MOD))
               (36 6 (:REWRITE DEFAULT-*-2))
               (34 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
               (34 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
               (22 2 (:DEFINITION NFIX))
               (18 2 (:REWRITE DEFAULT-NUMERATOR))
               (18 2 (:REWRITE DEFAULT-DENOMINATOR))
               (16 8 (:REWRITE SIMPLIFY-SUMS-<))
               (16 8
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (16 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (16 8 (:REWRITE DEFAULT-<-1))
               (12 12
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
               (12 12
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
               (11 11
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (11 11 (:REWRITE NORMALIZE-ADDENDS))
               (11 11 (:REWRITE DEFAULT-+-1))
               (11 11 (:REWRITE |(< (- x) (- y))|))
               (10 2 (:DEFINITION IFIX))
               (9 2 (:REWRITE DEFAULT-UNARY-/))
               (8 8 (:REWRITE DEFAULT-<-2))
               (6 6 (:REWRITE REDUCE-INTEGERP-+))
               (6 6
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (6 6 (:REWRITE INTEGERP-MINUS-X))
               (6 6 (:REWRITE DEFAULT-*-1))
               (6 6 (:REWRITE |(integerp (* c x))|))
               (6 6 (:REWRITE |(< (- x) 0)|))
               (6 6 (:META META-INTEGERP-CORRECT))
               (5 5 (:REWRITE |(equal (- x) (- y))|))
               (4 4
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (4 4 (:REWRITE |(equal (- x) 0)|))
               (4 4 (:REWRITE |(- (* c x))|))
               (3 3
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (3 3
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (3 3
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (3 3 (:REWRITE |(< 0 (- x))|))
               (2 2
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (2 2
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
               (1 1 (:REWRITE FOLD-CONSTS-IN-+))
               (1 1 (:REWRITE |(+ c (+ d x))|)))
(FLOOR-COMPLETION (14 14
                      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                  (14 14
                      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                  (14 14
                      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                  (14 14
                      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                  (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                  (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (14 14
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(FLOOR-0-LOCAL (1 1
                  (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
               (1 1
                  (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
               (1 1
                  (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
               (1 1
                  (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1)))
(MOD-COMPLETION (37 37 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                (2 2
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                (2 2 (:REWRITE |(+ 0 x)|))
                (1 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (1 1
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (1 1 (:REWRITE DEFAULT-+-1))
                (1 1 (:REWRITE |(equal (- x) (- y))|))
                (1 1 (:REWRITE |(equal (+ c x) d)|))
                (1 1 (:REWRITE |(+ c (+ d x))|)))
(MOD-0-LOCAL (33 33 (:TYPE-PRESCRIPTION INTEGERP-MOD))
             (4 4 (:REWRITE MOD-COMPLETION))
             (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
             (1 1
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (1 1
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (1 1
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (1 1 (:REWRITE DEFAULT-+-2))
             (1 1 (:REWRITE DEFAULT-+-1))
             (1 1 (:REWRITE |(equal (- x) (- y))|))
             (1 1 (:REWRITE |(equal (+ c x) d)|))
             (1 1 (:REWRITE |(+ c (+ d x))|))
             (1 1 (:REWRITE |(+ 0 x)|)))
(FLOOR-X-1-LOCAL (22 22
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                 (22 22
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                 (22 22
                     (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                 (22 22
                     (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                 (1 1 (:REWRITE REDUCE-INTEGERP-+))
                 (1 1 (:REWRITE INTEGERP-MINUS-X))
                 (1 1 (:META META-INTEGERP-CORRECT)))
(MOD-X-1-LOCAL (2 2 (:REWRITE MOD-COMPLETION))
               (1 1 (:REWRITE REDUCE-INTEGERP-+))
               (1 1 (:REWRITE INTEGERP-MINUS-X))
               (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
               (1 1 (:META META-INTEGERP-CORRECT)))
(FLOOR-MOD-ELIM-WEAK (21 21 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                     (4 2 (:REWRITE DEFAULT-*-2))
                     (2 2
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (2 2 (:REWRITE MOD-COMPLETION))
                     (2 2 (:REWRITE FLOOR-COMPLETION))
                     (2 2 (:REWRITE DEFAULT-*-1))
                     (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                     (2 1 (:REWRITE DEFAULT-+-2))
                     (1 1
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (1 1 (:REWRITE DEFAULT-+-1))
                     (1 1 (:REWRITE |(- (* c x))|)))
(FLOOR-INDUCT-FN (8432 100
                       (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                 (2091 2091
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (2091 2091
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (2091 2091
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (1580 100 (:DEFINITION NFIX))
                 (1220 394
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                 (1043 380 (:REWRITE DEFAULT-<-1))
                 (866 344 (:REWRITE DEFAULT-+-2))
                 (656 182 (:REWRITE DEFAULT-UNARY-MINUS))
                 (580 100 (:DEFINITION IFIX))
                 (527 380 (:REWRITE DEFAULT-<-2))
                 (527 59
                      (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                 (430 344 (:REWRITE DEFAULT-+-1))
                 (369 193 (:REWRITE DEFAULT-*-2))
                 (344 344
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (264 193 (:REWRITE DEFAULT-UNARY-/))
                 (225 193 (:REWRITE DEFAULT-*-1))
                 (193 193
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                 (193 193
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (162 162
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                 (151 59 (:REWRITE DEFAULT-NUMERATOR))
                 (151 59 (:REWRITE DEFAULT-DENOMINATOR))
                 (116 116 (:REWRITE ARITH-NORMALIZE-ADDENDS))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                 (105 105 (:META META-INTEGERP-CORRECT))
                 (77 77 (:REWRITE REDUCE-INTEGERP-+))
                 (77 77 (:REWRITE INTEGERP-MINUS-X))
                 (77 77 (:REWRITE |(integerp (* c x))|))
                 (66 32 (:REWRITE |(< d (+ c x))|))
                 (59 59 (:REWRITE |(< 0 (- x))|))
                 (27 27
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                 (24 24 (:REWRITE |(- (* c x))|))
                 (24 8 (:REWRITE |(< (+ d x) (+ c y))|))
                 (23 23 (:REWRITE |(equal (- x) (- y))|))
                 (14 14 (:REWRITE |arith (- (* c x))|))
                 (14 14
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                 (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (14 14
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (14 14
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (14 14 (:REWRITE |(equal (- x) 0)|))
                 (12 6 (:REWRITE |(< d (+ c x y))|))
                 (8 8 (:REWRITE |arith (* c (* d x))|))
                 (6 6 (:REWRITE FOLD-CONSTS-IN-+)))
(MOD-INDUCT-FN (8432 100
                     (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
               (2091 2091
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (2091 2091
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (2091 2091
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (1580 100 (:DEFINITION NFIX))
               (1220 394
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (1043 380 (:REWRITE DEFAULT-<-1))
               (866 344 (:REWRITE DEFAULT-+-2))
               (656 182 (:REWRITE DEFAULT-UNARY-MINUS))
               (580 100 (:DEFINITION IFIX))
               (527 380 (:REWRITE DEFAULT-<-2))
               (527 59
                    (:REWRITE INTEGERP==>DENOMINATOR-=-1))
               (430 344 (:REWRITE DEFAULT-+-1))
               (369 193 (:REWRITE DEFAULT-*-2))
               (344 344
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (264 193 (:REWRITE DEFAULT-UNARY-/))
               (225 193 (:REWRITE DEFAULT-*-1))
               (193 193
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
               (193 193
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (162 162
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (151 59 (:REWRITE DEFAULT-NUMERATOR))
               (151 59 (:REWRITE DEFAULT-DENOMINATOR))
               (116 116 (:REWRITE ARITH-NORMALIZE-ADDENDS))
               (110 110
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (110 110
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (110 110
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (105 105 (:META META-INTEGERP-CORRECT))
               (77 77 (:REWRITE REDUCE-INTEGERP-+))
               (77 77 (:REWRITE INTEGERP-MINUS-X))
               (77 77 (:REWRITE |(integerp (* c x))|))
               (66 32 (:REWRITE |(< d (+ c x))|))
               (59 59 (:REWRITE |(< 0 (- x))|))
               (27 27
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (24 24 (:REWRITE |(- (* c x))|))
               (24 8 (:REWRITE |(< (+ d x) (+ c y))|))
               (23 23 (:REWRITE |(equal (- x) (- y))|))
               (14 14 (:REWRITE |arith (- (* c x))|))
               (14 14
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (14 14
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (14 14
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (14 14 (:REWRITE |(equal (- x) 0)|))
               (12 6 (:REWRITE |(< d (+ c x y))|))
               (8 8 (:REWRITE |arith (* c (* d x))|))
               (6 6 (:REWRITE FOLD-CONSTS-IN-+)))
(FLOOR-IND)
(MOD-IND)
(FLOOR-BOUNDS-1 (4336 64
                      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                (785 785
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (785 785
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (785 785
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (704 64 (:DEFINITION NFIX))
                (666 173 (:REWRITE DEFAULT-+-2))
                (468 205 (:REWRITE DEFAULT-<-1))
                (368 112 (:REWRITE DEFAULT-UNARY-MINUS))
                (344 228
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (320 64 (:DEFINITION IFIX))
                (296 228
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (294 134 (:REWRITE DEFAULT-*-2))
                (280 136 (:REWRITE DEFAULT-UNARY-/))
                (230 205 (:REWRITE DEFAULT-<-2))
                (222 222 (:REWRITE |(< (- x) (- y))|))
                (173 173
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (173 173 (:REWRITE DEFAULT-+-1))
                (136 136
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (134 134
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (134 134 (:REWRITE DEFAULT-*-1))
                (122 122
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (122 122
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (122 122
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (109 109 (:REWRITE |(< (- x) 0)|))
                (105 105
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (54 22
                    (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                (43 43 (:REWRITE |(equal (- x) (- y))|))
                (41 41 (:REWRITE |(equal (- x) 0)|))
                (37 37
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (37 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (37 37
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (37 37
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (30 30 (:REWRITE REDUCE-INTEGERP-+))
                (30 30 (:REWRITE INTEGERP-MINUS-X))
                (30 30 (:REWRITE |(integerp (* c x))|))
                (30 30 (:META META-INTEGERP-CORRECT))
                (30 22 (:REWRITE DEFAULT-NUMERATOR))
                (30 22 (:REWRITE DEFAULT-DENOMINATOR))
                (26 26 (:REWRITE |(- (* c x))|))
                (21 21 (:REWRITE |(< 0 (- x))|))
                (20 9 (:REWRITE |(< d (+ c x))|))
                (18 11 (:REWRITE |(< (+ c x) d)|))
                (17 17
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (16 16 (:REWRITE |arith (- (* c x))|))
                (16 16 (:REWRITE ARITH-NORMALIZE-ADDENDS))
                (8 8 (:REWRITE |(* c (* d x))|))
                (7 7 (:REWRITE FOLD-CONSTS-IN-+))
                (7 7 (:REWRITE |(< (+ c x y) d)|))
                (6 6 (:REWRITE |arith (* c (* d x))|))
                (2 2 (:REWRITE |arith (+ c (+ d x))|))
                (2 1 (:REWRITE |(< (+ d x) (+ c y))|))
                (2 1 (:REWRITE |(< (+ c x) (+ d y))|)))
(FLOOR-BOUNDS-2 (26 26
                    (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (26 26
                    (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (26 26
                    (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                (26 26
                    (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (15 3 (:REWRITE DEFAULT-UNARY-/))
                (3 3
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (3 3
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (3 3 (:REWRITE DEFAULT-*-2))
                (3 3 (:REWRITE DEFAULT-*-1))
                (2 2
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (2 2
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (2 2
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (2 2 (:REWRITE |(equal (- x) 0)|))
                (2 2 (:REWRITE |(equal (- x) (- y))|))
                (1 1 (:REWRITE REDUCE-INTEGERP-+))
                (1 1 (:REWRITE INTEGERP-MINUS-X))
                (1 1 (:REWRITE |(integerp (* c x))|))
                (1 1 (:META META-INTEGERP-CORRECT)))
(FLOOR-BOUNDS-3 (2168 32
                      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                (352 32 (:DEFINITION NFIX))
                (337 90 (:REWRITE DEFAULT-+-2))
                (330 330
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (330 330
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (330 330
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (244 102
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (240 100 (:REWRITE SIMPLIFY-SUMS-<))
                (233 100 (:REWRITE DEFAULT-<-1))
                (223 107
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (177 52 (:REWRITE DEFAULT-UNARY-MINUS))
                (160 32 (:DEFINITION IFIX))
                (143 63 (:REWRITE DEFAULT-*-2))
                (123 63 (:REWRITE DEFAULT-UNARY-/))
                (107 107
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (107 100 (:REWRITE DEFAULT-<-2))
                (105 105 (:REWRITE |(< (- x) (- y))|))
                (90 90
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (90 90 (:REWRITE DEFAULT-+-1))
                (63 63
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (63 63
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (63 63 (:REWRITE DEFAULT-*-1))
                (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (51 51 (:REWRITE |(< (- x) 0)|))
                (49 49
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (16 16
                    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
                (16 16 (:REWRITE |(equal (- x) 0)|))
                (16 16 (:REWRITE |(equal (- x) (- y))|))
                (15 15
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (15 15
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (15 15
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (15 15 (:REWRITE |(< 0 (- x))|))
                (15 8 (:REWRITE |(< d (+ c x))|))
                (14 14
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (12 12 (:REWRITE |(- (* c x))|))
                (11 11 (:REWRITE REDUCE-INTEGERP-+))
                (11 11 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                (11 11
                    (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                (11 11 (:REWRITE INTEGERP-MINUS-X))
                (11 11 (:REWRITE DEFAULT-NUMERATOR))
                (11 11 (:REWRITE DEFAULT-DENOMINATOR))
                (11 11 (:REWRITE |(integerp (* c x))|))
                (11 11 (:META META-INTEGERP-CORRECT))
                (10 10 (:REWRITE ARITH-NORMALIZE-ADDENDS))
                (7 7 (:REWRITE FOLD-CONSTS-IN-+))
                (7 7 (:REWRITE |(< d (+ c x y))|))
                (4 4 (:REWRITE |arith (* c (* d x))|))
                (2 2 (:REWRITE |arith (- (* c x))|))
                (2 2 (:REWRITE |arith (+ c (+ d x))|))
                (2 1 (:REWRITE |(< (+ c x) d)|)))
(MOD-BOUNDS-1 (1072 16
                    (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
              (358 358
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (358 358
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (358 358
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (358 358
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (176 16 (:DEFINITION NFIX))
              (163 62 (:REWRITE DEFAULT-+-2))
              (156 84 (:REWRITE DEFAULT-<-1))
              (100 84 (:REWRITE DEFAULT-<-2))
              (97 97 (:REWRITE |(< (- x) (- y))|))
              (84 60 (:REWRITE DEFAULT-*-2))
              (84 38 (:REWRITE DEFAULT-UNARY-MINUS))
              (80 16 (:DEFINITION IFIX))
              (62 62
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (62 62 (:REWRITE DEFAULT-+-1))
              (60 60
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (60 60 (:REWRITE DEFAULT-*-1))
              (53 53 (:REWRITE |arith (* c (* d x))|))
              (46 46
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (46 46 (:REWRITE DEFAULT-UNARY-/))
              (46 46 (:REWRITE |(< (- x) 0)|))
              (46 14
                  (:REWRITE INTEGERP==>DENOMINATOR-=-1))
              (40 40
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (27 27 (:REWRITE |arith (- (* c x))|))
              (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (22 22 (:REWRITE REDUCE-INTEGERP-+))
              (22 22 (:REWRITE INTEGERP-MINUS-X))
              (22 22 (:REWRITE |(integerp (* c x))|))
              (22 22 (:META META-INTEGERP-CORRECT))
              (22 14 (:REWRITE DEFAULT-NUMERATOR))
              (22 14 (:REWRITE DEFAULT-DENOMINATOR))
              (20 20 (:REWRITE |(< 0 (- x))|))
              (18 18
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (14 14 (:REWRITE |(+ c (+ d x))|))
              (13 13 (:REWRITE |(< (+ c x) d)|))
              (12 12 (:REWRITE ARITH-NORMALIZE-ADDENDS))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
              (6 6 (:REWRITE |(< d (+ c x))|))
              (6 6 (:REWRITE |(- (* c x))|))
              (5 5 (:REWRITE FOLD-CONSTS-IN-+))
              (5 5 (:REWRITE |(equal (- x) (- y))|))
              (5 5 (:REWRITE |(< (+ c x y) d)|))
              (4 4 (:REWRITE MOD-COMPLETION))
              (3 3
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (3 3
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (3 3
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (3 3 (:REWRITE |(equal (- x) 0)|))
              (2 2 (:REWRITE FLOOR-COMPLETION))
              (2 2 (:REWRITE |(* c (* d x))|))
              (1 1 (:REWRITE |arith (+ c (+ d x))|)))
(MOD-BOUNDS-2 (936 14
                   (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
              (334 334
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (334 334
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (334 334
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (334 334
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (154 14 (:DEFINITION NFIX))
              (146 74 (:REWRITE DEFAULT-<-1))
              (143 55 (:REWRITE DEFAULT-+-2))
              (87 87 (:REWRITE |(< (- x) (- y))|))
              (80 74 (:REWRITE DEFAULT-<-2))
              (74 52 (:REWRITE DEFAULT-*-2))
              (72 34 (:REWRITE DEFAULT-UNARY-MINUS))
              (70 14 (:DEFINITION IFIX))
              (55 55 (:REWRITE |arith (* c (* d x))|))
              (55 55
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (55 55 (:REWRITE DEFAULT-+-1))
              (52 52
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (52 52 (:REWRITE DEFAULT-*-1))
              (44 12
                  (:REWRITE INTEGERP==>DENOMINATOR-=-1))
              (43 43 (:REWRITE |(< (- x) 0)|))
              (40 40
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (40 40 (:REWRITE DEFAULT-UNARY-/))
              (39 39
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (35 35 (:REWRITE |arith (- (* c x))|))
              (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (20 20 (:REWRITE REDUCE-INTEGERP-+))
              (20 20 (:REWRITE INTEGERP-MINUS-X))
              (20 20 (:REWRITE |(integerp (* c x))|))
              (20 20 (:META META-INTEGERP-CORRECT))
              (20 12 (:REWRITE DEFAULT-NUMERATOR))
              (20 12 (:REWRITE DEFAULT-DENOMINATOR))
              (15 15 (:REWRITE |(< 0 (- x))|))
              (13 13 (:REWRITE |(+ c (+ d x))|))
              (12 12 (:REWRITE ARITH-NORMALIZE-ADDENDS))
              (11 11
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (11 11 (:REWRITE |(< d (+ c x))|))
              (9 9 (:REWRITE |(equal (- x) (- y))|))
              (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
              (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
              (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
              (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
              (7 7
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (7 7
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (7 7
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (7 7 (:REWRITE |(equal (- x) 0)|))
              (6 6 (:REWRITE |(< (+ c x) d)|))
              (6 6 (:REWRITE |(- (* c x))|))
              (4 4 (:REWRITE MOD-COMPLETION))
              (4 4 (:REWRITE FOLD-CONSTS-IN-+))
              (4 4 (:REWRITE |(< d (+ c x y))|))
              (2 2 (:REWRITE FLOOR-COMPLETION))
              (2 2 (:REWRITE |(* c (* d x))|))
              (1 1 (:REWRITE |arith (+ c (+ d x))|)))
(MOD-BOUNDS-3 (40 4 (:LINEAR MOD-BOUNDS-2))
              (40 4 (:LINEAR MOD-BOUNDS-1))
              (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (8 8 (:REWRITE SIMPLIFY-SUMS-<))
              (8 8
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
              (8 8
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
              (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (8 8 (:REWRITE DEFAULT-<-2))
              (8 8 (:REWRITE DEFAULT-<-1))
              (8 8 (:REWRITE |(< (- x) (- y))|))
              (4 4
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (4 4
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (4 4 (:REWRITE |(< 0 (- x))|))
              (4 4 (:REWRITE |(< (- x) 0)|))
              (2 2
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (2 2
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (2 2 (:REWRITE MOD-COMPLETION))
              (2 2 (:REWRITE DEFAULT-UNARY-/))
              (2 2 (:REWRITE DEFAULT-*-2))
              (2 2 (:REWRITE DEFAULT-*-1))
              (1 1
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (1 1
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (1 1 (:REWRITE REDUCE-INTEGERP-+))
              (1 1
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (1 1 (:REWRITE INTEGERP-MINUS-X))
              (1 1 (:REWRITE FLOOR-COMPLETION))
              (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
              (1 1 (:REWRITE |(integerp (* c x))|))
              (1 1 (:REWRITE |(equal (- x) 0)|))
              (1 1 (:REWRITE |(equal (- x) (- y))|))
              (1 1 (:META META-INTEGERP-CORRECT)))
(FLOOR-NONNEGATIVE-1 (28 4 (:REWRITE DEFAULT-UNARY-/))
                     (28 1 (:LINEAR FLOOR-BOUNDS-3))
                     (28 1 (:LINEAR FLOOR-BOUNDS-2))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (5 1 (:REWRITE DEFAULT-+-2))
                     (4 4
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (4 4
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (4 4
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (4 4
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                     (4 4
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (4 4 (:REWRITE DEFAULT-*-2))
                     (4 4 (:REWRITE DEFAULT-*-1))
                     (4 4 (:REWRITE |(equal (- x) 0)|))
                     (4 4 (:REWRITE |(equal (- x) (- y))|))
                     (2 2 (:REWRITE REDUCE-INTEGERP-+))
                     (2 2 (:REWRITE INTEGERP-MINUS-X))
                     (2 2 (:REWRITE FLOOR-COMPLETION))
                     (2 2 (:REWRITE |(integerp (* c x))|))
                     (2 2 (:META META-INTEGERP-CORRECT))
                     (1 1
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (1 1 (:REWRITE NORMALIZE-ADDENDS))
                     (1 1 (:REWRITE DEFAULT-+-1)))
(FLOOR-NONNEGATIVE-2 (28 4 (:REWRITE DEFAULT-UNARY-/))
                     (28 1 (:LINEAR FLOOR-BOUNDS-3))
                     (28 1 (:LINEAR FLOOR-BOUNDS-2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (5 1 (:REWRITE DEFAULT-+-2))
                     (4 4
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (4 4
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (4 4
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (4 4
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                     (4 4
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (4 4 (:REWRITE DEFAULT-*-2))
                     (4 4 (:REWRITE DEFAULT-*-1))
                     (4 4 (:REWRITE |(equal (- x) 0)|))
                     (4 4 (:REWRITE |(equal (- x) (- y))|))
                     (2 2 (:REWRITE REDUCE-INTEGERP-+))
                     (2 2 (:REWRITE INTEGERP-MINUS-X))
                     (2 2 (:REWRITE FLOOR-COMPLETION))
                     (2 2 (:REWRITE |(integerp (* c x))|))
                     (2 2 (:META META-INTEGERP-CORRECT))
                     (1 1
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (1 1 (:REWRITE NORMALIZE-ADDENDS))
                     (1 1 (:REWRITE DEFAULT-+-1)))
(FLOOR-NONPOSITIVE-1 (28 1 (:LINEAR FLOOR-BOUNDS-3))
                     (28 1 (:LINEAR FLOOR-BOUNDS-2))
                     (21 3 (:REWRITE DEFAULT-UNARY-/))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (3 3
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (3 3
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (3 3
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                     (3 3
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (3 3 (:REWRITE DEFAULT-*-2))
                     (3 3 (:REWRITE DEFAULT-*-1))
                     (3 3 (:REWRITE |(equal (- x) 0)|))
                     (3 3 (:REWRITE |(equal (- x) (- y))|))
                     (2 2 (:REWRITE REDUCE-INTEGERP-+))
                     (2 2 (:REWRITE INTEGERP-MINUS-X))
                     (2 2 (:REWRITE |(integerp (* c x))|))
                     (2 2 (:META META-INTEGERP-CORRECT))
                     (1 1 (:REWRITE FLOOR-COMPLETION)))
(FLOOR-NONPOSITIVE-2 (28 1 (:LINEAR FLOOR-BOUNDS-3))
                     (28 1 (:LINEAR FLOOR-BOUNDS-2))
                     (21 3 (:REWRITE DEFAULT-UNARY-/))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (3 3
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (3 3
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (3 3
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                     (3 3
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (3 3 (:REWRITE DEFAULT-*-2))
                     (3 3 (:REWRITE DEFAULT-*-1))
                     (3 3 (:REWRITE |(equal (- x) 0)|))
                     (3 3 (:REWRITE |(equal (- x) (- y))|))
                     (2 2 (:REWRITE REDUCE-INTEGERP-+))
                     (2 2 (:REWRITE INTEGERP-MINUS-X))
                     (2 2 (:REWRITE |(integerp (* c x))|))
                     (2 2 (:META META-INTEGERP-CORRECT))
                     (1 1 (:REWRITE FLOOR-COMPLETION)))
(FLOOR-POSITIVE (964 964
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (891 38 (:LINEAR FLOOR-BOUNDS-3))
                (572 572
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                (572 572
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                (374 158 (:REWRITE DEFAULT-UNARY-/))
                (272 160
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (196 196
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (196 196 (:REWRITE DEFAULT-*-2))
                (196 196 (:REWRITE DEFAULT-*-1))
                (195 87 (:REWRITE DEFAULT-+-2))
                (179 125 (:REWRITE DEFAULT-<-2))
                (158 158
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (145 145 (:REWRITE |(< (- x) (- y))|))
                (131 11 (:REWRITE FLOOR-NONPOSITIVE-1))
                (129 11 (:REWRITE FLOOR-NONPOSITIVE-2))
                (125 125 (:REWRITE DEFAULT-<-1))
                (118 64 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (118 64
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (118 64
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (87 87
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (87 87 (:REWRITE DEFAULT-+-1))
                (84 84 (:REWRITE INTEGERP-MINUS-X))
                (84 84 (:META META-INTEGERP-CORRECT))
                (76 76 (:REWRITE |(integerp (* c x))|))
                (67 67 (:REWRITE FLOOR-COMPLETION))
                (64 64
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (64 64 (:REWRITE |(equal (- x) 0)|))
                (64 64 (:REWRITE |(equal (- x) (- y))|))
                (52 52 (:REWRITE |(< 0 (- x))|))
                (50 50
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (36 36 (:REWRITE |(< (- x) 0)|))
                (34 34
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
                (16 16 (:REWRITE |arith (* c (* d x))|))
                (16 16 (:REWRITE ARITH-NORMALIZE-ADDENDS))
                (11 11 (:REWRITE |(< (+ c x) d)|))
                (9 9 (:REWRITE |(< d (+ c x))|))
                (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                (3 3 (:REWRITE |arith (- (* c x))|))
                (3 3 (:REWRITE |arith (* (- x) y)|))
                (2 2
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (2 2
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (2 2
                   (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
                (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
                (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
                (2 2 (:REWRITE |(< (+ c x y) d)|))
                (2 2 (:REWRITE |(* c (* d x))|)))
(FLOOR-NEGATIVE (155 155
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (155 155
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (137 7 (:LINEAR FLOOR-BOUNDS-3))
                (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (42 15 (:REWRITE DEFAULT-<-1))
                (25 19 (:REWRITE DEFAULT-UNARY-/))
                (24 4 (:REWRITE FLOOR-NONNEGATIVE-2))
                (24 4 (:REWRITE FLOOR-NONNEGATIVE-1))
                (22 15 (:REWRITE SIMPLIFY-SUMS-<))
                (22 15
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (22 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (19 19
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (18 18
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (18 18 (:REWRITE DEFAULT-*-2))
                (18 18 (:REWRITE DEFAULT-*-1))
                (15 15
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (15 15
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (15 15 (:REWRITE DEFAULT-<-2))
                (15 15 (:REWRITE |(< (- x) (- y))|))
                (12 12 (:REWRITE REDUCE-INTEGERP-+))
                (12 12 (:REWRITE INTEGERP-MINUS-X))
                (12 12 (:REWRITE |(integerp (* c x))|))
                (12 12 (:META META-INTEGERP-CORRECT))
                (9 9
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (9 9 (:REWRITE |(< (- x) 0)|))
                (7 7 (:REWRITE FLOOR-COMPLETION))
                (6 6
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (6 6 (:REWRITE |(< 0 (- x))|))
                (2 2
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (2 2
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (2 2
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (2 2
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (2 2 (:REWRITE |(equal (- x) (- y))|))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (1 1 (:REWRITE |(equal (- x) 0)|)))
(FLOOR-ZERO (622 32 (:LINEAR FLOOR-BOUNDS-3))
            (453 453
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (453 453
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (453 453
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (433 433
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
            (433 433
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
            (433 433
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
            (433 433
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
            (433 433
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
            (433 433
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
            (161 28 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (161 28
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (161 28
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (89 89
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (89 89 (:REWRITE DEFAULT-UNARY-/))
            (86 86
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (86 86 (:REWRITE DEFAULT-*-2))
            (86 86 (:REWRITE DEFAULT-*-1))
            (75 15 (:REWRITE DEFAULT-+-2))
            (56 56 (:REWRITE REDUCE-INTEGERP-+))
            (56 56 (:REWRITE INTEGERP-MINUS-X))
            (56 56 (:REWRITE |(integerp (* c x))|))
            (56 56 (:META META-INTEGERP-CORRECT))
            (48 48 (:REWRITE SIMPLIFY-SUMS-<))
            (48 48
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (48 48
                (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
            (48 48
                (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
            (48 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
            (48 48 (:REWRITE DEFAULT-<-2))
            (48 48 (:REWRITE DEFAULT-<-1))
            (48 48 (:REWRITE |(< (- x) (- y))|))
            (46 46 (:REWRITE FLOOR-COMPLETION))
            (28 28
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
            (28 28 (:REWRITE |(equal (- x) 0)|))
            (28 28 (:REWRITE |(equal (- x) (- y))|))
            (15 15
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (15 15 (:REWRITE NORMALIZE-ADDENDS))
            (15 15 (:REWRITE DEFAULT-+-1))
            (13 13
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
            (13 13 (:REWRITE |(< (- x) 0)|))
            (12 12 (:REWRITE ARITH-NORMALIZE-ADDENDS))
            (11 11
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
            (11 11 (:REWRITE |(< 0 (- x))|))
            (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD))
            (2 2 (:REWRITE |arith (- (* c x))|))
            (2 2 (:REWRITE |arith (* c (* d x))|))
            (2 2 (:REWRITE |arith (* (- x) y)|)))
(FLOOR-=-X/Y-1 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
               (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (40 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
               (40 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (40 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (40 40
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (33 3 (:REWRITE FLOOR-ZERO . 4))
               (33 3 (:REWRITE FLOOR-ZERO . 3))
               (23 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (23 7
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (23 7
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (22 4 (:REWRITE DEFAULT-UNARY-/))
               (21 3 (:REWRITE FLOOR-ZERO . 2))
               (7 7 (:REWRITE |(equal (- x) (- y))|))
               (6 6
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (6 6 (:REWRITE SIMPLIFY-SUMS-<))
               (6 6
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (6 6
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
               (6 6
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
               (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (6 6 (:REWRITE DEFAULT-<-2))
               (6 6 (:REWRITE DEFAULT-<-1))
               (6 6 (:REWRITE |(equal (- x) 0)|))
               (6 6 (:REWRITE |(< (- x) (- y))|))
               (4 4
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
               (4 4
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (4 4 (:REWRITE DEFAULT-*-2))
               (4 4 (:REWRITE DEFAULT-*-1))
               (3 3
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (3 3
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (3 3 (:REWRITE FLOOR-COMPLETION))
               (3 3 (:REWRITE |(< 0 (- x))|))
               (3 3 (:REWRITE |(< (- x) 0)|))
               (2 2 (:LINEAR FLOOR-BOUNDS-3))
               (1 1 (:REWRITE REDUCE-INTEGERP-+))
               (1 1 (:REWRITE INTEGERP-MINUS-X))
               (1 1 (:REWRITE |(integerp (* c x))|))
               (1 1 (:META META-INTEGERP-CORRECT)))
(FLOOR-=-X/Y-2 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
               (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (22 22 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
               (22 22 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (22 22 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (22 22
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
               (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (11 1 (:REWRITE FLOOR-ZERO . 4))
               (11 1 (:REWRITE FLOOR-ZERO . 3))
               (9 3 (:REWRITE DEFAULT-UNARY-/))
               (7 1 (:REWRITE FLOOR-ZERO . 2))
               (3 3
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
               (3 3
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (3 3 (:REWRITE DEFAULT-*-2))
               (3 3 (:REWRITE DEFAULT-*-1))
               (2 2
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (2 2 (:REWRITE SIMPLIFY-SUMS-<))
               (2 2
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (2 2
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (2 2
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
               (2 2
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
               (2 2 (:REWRITE REDUCE-INTEGERP-+))
               (2 2
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (2 2 (:REWRITE INTEGERP-MINUS-X))
               (2 2 (:REWRITE DEFAULT-<-2))
               (2 2 (:REWRITE DEFAULT-<-1))
               (2 2 (:REWRITE |(integerp (* c x))|))
               (2 2 (:REWRITE |(equal (- x) 0)|))
               (2 2 (:REWRITE |(equal (- x) (- y))|))
               (2 2 (:REWRITE |(< (- x) (- y))|))
               (2 2 (:META META-INTEGERP-CORRECT))
               (1 1
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (1 1
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (1 1 (:REWRITE FLOOR-COMPLETION))
               (1 1 (:REWRITE |(< 0 (- x))|))
               (1 1 (:REWRITE |(< (- x) 0)|)))
(MOD-NONNEGATIVE (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(MOD-NONPOSITIVE (7 7 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                 (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(MOD-POSITIVE (607 607
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (607 607
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (458 458 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (266 50 (:LINEAR MOD-BOUNDS-2))
              (139 95 (:REWRITE DEFAULT-<-2))
              (104 104 (:REWRITE |(< (- x) (- y))|))
              (97 25 (:LINEAR MOD-BOUNDS-3))
              (95 95 (:REWRITE DEFAULT-<-1))
              (92 11 (:REWRITE MOD-NONPOSITIVE))
              (61 61
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
              (58 58 (:REWRITE MOD-COMPLETION))
              (53 37 (:REWRITE DEFAULT-+-2))
              (52 28 (:REWRITE DEFAULT-UNARY-/))
              (51 51 (:REWRITE |(< 0 (- x))|))
              (50 50
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (50 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (50 26
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (50 26
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (49 49
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (49 49 (:REWRITE DEFAULT-*-2))
              (49 49 (:REWRITE DEFAULT-*-1))
              (43 43 (:REWRITE |(< (- x) 0)|))
              (42 42
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (37 37
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (37 37 (:REWRITE DEFAULT-+-1))
              (28 28
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (26 26
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (26 26 (:REWRITE |(equal (- x) 0)|))
              (26 26 (:REWRITE |(equal (- x) (- y))|))
              (16 16 (:REWRITE INTEGERP-MINUS-X))
              (16 16 (:META META-INTEGERP-CORRECT))
              (11 11 (:REWRITE |(integerp (* c x))|))
              (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
              (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
              (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
              (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
              (6 6
                 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
              (4 4 (:REWRITE |(< d (+ c x))|))
              (4 4 (:REWRITE |(< (+ c x) d)|))
              (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
              (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (2 2
                 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
              (1 1 (:REWRITE FOLD-CONSTS-IN-+))
              (1 1 (:REWRITE |(< (+ d x) (+ c y))|))
              (1 1 (:REWRITE |(< (+ c x) (+ d y))|))
              (1 1 (:REWRITE |(< (+ c x y) d)|)))
(MOD-NEGATIVE (632 632
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (618 618
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (462 458
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
              (458 458
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (458 458 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (266 50 (:LINEAR MOD-BOUNDS-1))
              (160 94 (:REWRITE DEFAULT-<-1))
              (103 103 (:REWRITE |(< (- x) (- y))|))
              (97 25 (:LINEAR MOD-BOUNDS-3))
              (94 94 (:REWRITE DEFAULT-<-2))
              (92 11 (:REWRITE MOD-NONNEGATIVE))
              (62 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (62 26
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (62 26
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (58 58 (:REWRITE MOD-COMPLETION))
              (55 39 (:REWRITE DEFAULT-+-2))
              (52 28 (:REWRITE DEFAULT-UNARY-/))
              (51 51
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (51 51 (:REWRITE DEFAULT-*-2))
              (51 51 (:REWRITE DEFAULT-*-1))
              (51 51 (:REWRITE |(< (- x) 0)|))
              (50 50
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (42 42 (:REWRITE |(< 0 (- x))|))
              (41 41
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (39 39
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (39 39 (:REWRITE DEFAULT-+-1))
              (28 28
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (26 26
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (26 26 (:REWRITE |(equal (- x) 0)|))
              (26 26 (:REWRITE |(equal (- x) (- y))|))
              (16 16 (:REWRITE INTEGERP-MINUS-X))
              (16 16 (:META META-INTEGERP-CORRECT))
              (11 11 (:REWRITE |(integerp (* c x))|))
              (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
              (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
              (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
              (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
              (9 9
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
              (5 5 (:REWRITE |(< (+ c x) d)|))
              (3 3 (:REWRITE |(< d (+ c x))|))
              (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
              (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
              (2 2
                 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
              (1 1 (:REWRITE FOLD-CONSTS-IN-+))
              (1 1 (:REWRITE |(< (+ d x) (+ c y))|))
              (1 1 (:REWRITE |(< (+ c x) (+ d y))|))
              (1 1 (:REWRITE |(< (+ c x y) d)|)))
(MOD-ZERO (224 224
               (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (224 224
               (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (224 224
               (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (220 22 (:LINEAR MOD-BOUNDS-2))
          (220 22 (:LINEAR MOD-BOUNDS-1))
          (171 171
               (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
          (171 171
               (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
          (171 171
               (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
          (171 171
               (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
          (171 171
               (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
          (171 171
               (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
          (171 171 (:TYPE-PRESCRIPTION INTEGERP-MOD))
          (87 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (87 39
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (87 39
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (77 11 (:LINEAR MOD-BOUNDS-3))
          (59 17 (:REWRITE DEFAULT-UNARY-/))
          (52 52
              (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
          (52 52 (:REWRITE |(< (- x) (- y))|))
          (49 49 (:REWRITE DEFAULT-<-2))
          (49 49 (:REWRITE DEFAULT-<-1))
          (39 39
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
          (39 39 (:REWRITE |(equal (- x) 0)|))
          (39 39 (:REWRITE |(equal (- x) (- y))|))
          (25 25
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
          (25 25 (:REWRITE |(< 0 (- x))|))
          (24 24
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
          (24 24 (:REWRITE |(< (- x) 0)|))
          (21 21
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
          (21 21 (:REWRITE DEFAULT-*-2))
          (21 21 (:REWRITE DEFAULT-*-1))
          (17 17
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
          (12 12 (:REWRITE MOD-COMPLETION))
          (8 8
             (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
          (8 8 (:REWRITE REDUCE-INTEGERP-+))
          (8 8 (:REWRITE INTEGERP-MINUS-X))
          (8 8 (:META META-INTEGERP-CORRECT))
          (7 7 (:REWRITE |(integerp (* c x))|))
          (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
          (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
          (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
          (3 3
             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
          (2 2
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
          (2 2 (:REWRITE DEFAULT-+-2))
          (2 2 (:REWRITE DEFAULT-+-1))
          (1 1 (:REWRITE |(< d (+ c x))|))
          (1 1 (:REWRITE |(< (+ c x) d)|)))
(MOD-X-Y-=-X (2370 698 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
             (1222 698
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
             (1222 698
                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
             (1195 1195
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
             (1195 1195
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
             (1182 1182
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
             (698 698 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
             (698 698
                  (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
             (698 698
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
             (698 698 (:TYPE-PRESCRIPTION INTEGERP-MOD))
             (359 65 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (359 65
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (359 65
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (248 44 (:REWRITE MOD-ZERO . 3))
             (118 118 (:REWRITE SIMPLIFY-SUMS-<))
             (118 118
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
             (118 118
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
             (118 118
                  (:REWRITE PREFER-POSITIVE-ADDENDS-<))
             (118 118 (:REWRITE DEFAULT-<-2))
             (118 118 (:REWRITE DEFAULT-<-1))
             (118 118 (:REWRITE |(< (- x) (- y))|))
             (94 94
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (94 94 (:REWRITE DEFAULT-*-2))
             (94 94 (:REWRITE DEFAULT-*-1))
             (89 89
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
             (89 89 (:REWRITE DEFAULT-UNARY-/))
             (86 86 (:REWRITE MOD-COMPLETION))
             (65 65 (:REWRITE INTEGERP-MINUS-X))
             (65 65 (:REWRITE |(equal (- x) (- y))|))
             (65 65 (:META META-INTEGERP-CORRECT))
             (61 61 (:REWRITE |(integerp (* c x))|))
             (54 54
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
             (47 47
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
             (47 47 (:REWRITE |(< (- x) 0)|))
             (46 46
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
             (46 46 (:REWRITE |(equal (- x) 0)|))
             (45 45
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
             (45 45 (:REWRITE |(< 0 (- x))|))
             (27 11 (:REWRITE DEFAULT-+-2))
             (12 12
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
             (12 12
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
             (12 12
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
             (12 12
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
             (11 11
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (11 11 (:REWRITE DEFAULT-+-1))
             (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
             (6 6
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
             (6 6
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
             (6 6
                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
             (6 6
                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
             (2 2
                (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
             (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
             (2 2 (:REWRITE |(+ c (+ d x))|)))
(JUSTIFY-FLOOR-RECURSION
     (215 215 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (215 215 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (215 215 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (215 215
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (215 215
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (215 215
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (176 8 (:LINEAR FLOOR-BOUNDS-3))
     (176 8 (:LINEAR FLOOR-BOUNDS-2))
     (126 126
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (126 126
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (126 126
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (112 12
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (60 18 (:REWRITE SIMPLIFY-SUMS-<))
     (60 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (60 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (54 12 (:REWRITE FLOOR-ZERO . 3))
     (42 18 (:REWRITE DEFAULT-<-1))
     (36 18 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (24 24
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:REWRITE DEFAULT-UNARY-/))
     (24 24 (:REWRITE DEFAULT-*-2))
     (24 24 (:REWRITE DEFAULT-*-1))
     (24 24 (:META META-INTEGERP-CORRECT))
     (20 4 (:REWRITE DEFAULT-+-2))
     (18 18
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (18 18 (:REWRITE |(< (- x) (- y))|))
     (16 16 (:REWRITE |(integerp (* c x))|))
     (12 12 (:REWRITE FLOOR-ZERO . 4))
     (12 12 (:REWRITE FLOOR-ZERO . 2))
     (12 12 (:REWRITE FLOOR-COMPLETION))
     (12 12
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (4 4 (:REWRITE |arith (* c (* d x))|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2 (:REWRITE |arith (- (* c x))|))
     (2 2 (:REWRITE |arith (* (- x) y)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (2 2 (:REWRITE |(< 0 (- x))|)))
(FLOOR-+-WEAK (10388 174 (:REWRITE FLOOR-ZERO . 4))
              (10388 174 (:REWRITE FLOOR-ZERO . 3))
              (10370 3666 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
              (7029 1058 (:REWRITE DEFAULT-+-2))
              (5765 5765
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (3666 3666 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
              (3666 3666 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (3661 3661
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (3658 3658
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
              (2652 852 (:REWRITE DEFAULT-*-2))
              (2382 2382
                    (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
              (2382 2382
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
              (2382 2382
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
              (2382 2382
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
              (2382 2382
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
              (2373 2373
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
              (2373 2373
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
              (2284 1058 (:REWRITE DEFAULT-+-1))
              (1311 219
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (1311 219
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (1275 527 (:REWRITE DEFAULT-<-2))
              (1275 527 (:REWRITE DEFAULT-<-1))
              (1218 174 (:REWRITE FLOOR-ZERO . 2))
              (1176 272 (:META META-INTEGERP-CORRECT))
              (1124 174 (:REWRITE FLOOR-COMPLETION))
              (1058 1058
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (995 497 (:REWRITE DEFAULT-UNARY-/))
              (852 852
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (852 852 (:REWRITE DEFAULT-*-1))
              (643 74 (:REWRITE MOD-ZERO . 2))
              (580 580
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
              (572 109 (:LINEAR MOD-BOUNDS-3))
              (570 570 (:REWRITE |(< (- x) (- y))|))
              (530 530
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (530 530
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (530 530
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (497 497
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (374 74 (:REWRITE MOD-X-Y-=-X . 4))
              (374 74 (:REWRITE MOD-X-Y-=-X . 3))
              (353 353 (:REWRITE FOLD-CONSTS-IN-+))
              (272 272 (:REWRITE INTEGERP-MINUS-X))
              (254 74 (:REWRITE MOD-ZERO . 3))
              (238 238 (:REWRITE |(< 0 (- x))|))
              (235 235 (:REWRITE |(< (- x) 0)|))
              (234 234
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (231 231
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (219 219 (:REWRITE |(equal (- x) (- y))|))
              (195 195
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (195 195 (:REWRITE |(equal (- x) 0)|))
              (149 149 (:REWRITE ARITH-NORMALIZE-ADDENDS))
              (148 148 (:REWRITE MOD-COMPLETION))
              (143 143 (:REWRITE |(< (+ c x) d)|))
              (142 142
                   (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
              (133 133 (:REWRITE |(< d (+ c x))|))
              (108 108 (:REWRITE |(integerp (* c x))|))
              (74 74 (:REWRITE MOD-X-Y-=-X . 2))
              (70 46 (:REWRITE DEFAULT-UNARY-MINUS))
              (60 60 (:REWRITE |(< (+ c x y) d)|))
              (52 52 (:REWRITE |(< d (+ c x y))|))
              (40 40 (:REWRITE |(* c (* d x))|))
              (36 36 (:REWRITE |arith (* c (* d x))|))
              (27 27 (:REWRITE |arith (+ c (+ d x))|))
              (21 21 (:REWRITE |(equal (+ c x) d)|))
              (20 20 (:REWRITE |arith (* (- x) y)|))
              (19 19 (:REWRITE |(equal (+ c x y) d)|))
              (14 14 (:REWRITE |arith (- (* c x))|))
              (14 14 (:REWRITE MOD-POSITIVE . 3))
              (14 14 (:REWRITE MOD-POSITIVE . 2))
              (14 14 (:REWRITE MOD-NEGATIVE . 3))
              (14 14 (:REWRITE MOD-NEGATIVE . 2))
              (13 13 (:REWRITE MOD-NONPOSITIVE))
              (13 13 (:REWRITE MOD-NONNEGATIVE))
              (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
              (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
              (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
              (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
              (6 6 (:REWRITE |(< (+ d x) (+ c y))|))
              (6 6 (:REWRITE |(< (+ c x) (+ d y))|)))
(MOD-+-WEAK (5406 78 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
            (2973 19 (:REWRITE FLOOR-ZERO . 4))
            (2973 19 (:REWRITE FLOOR-ZERO . 3))
            (2735 163 (:REWRITE DEFAULT-+-2))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
            (1180 1180
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
            (1178 4 (:LINEAR FLOOR-BOUNDS-3))
            (1178 4 (:LINEAR FLOOR-BOUNDS-2))
            (1051 163 (:REWRITE DEFAULT-+-1))
            (942 78
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (660 4 (:REWRITE MOD-ZERO . 3))
            (597 4 (:REWRITE MOD-X-Y-=-X . 4))
            (597 4 (:REWRITE MOD-X-Y-=-X . 3))
            (536 16 (:META META-INTEGERP-CORRECT))
            (398 62 (:REWRITE DEFAULT-*-2))
            (392 32 (:REWRITE DEFAULT-UNARY-MINUS))
            (342 54 (:REWRITE SIMPLIFY-SUMS-<))
            (275 179
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (210 138 (:TYPE-PRESCRIPTION INTEGERP-MOD))
            (205 205 (:REWRITE |(+ c (+ d x))|))
            (198 54 (:REWRITE DEFAULT-<-2))
            (198 54 (:REWRITE DEFAULT-<-1))
            (179 179
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (179 179
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (179 179
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (163 163
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (163 19 (:REWRITE FLOOR-ZERO . 2))
            (139 19 (:REWRITE FLOOR-COMPLETION))
            (138 138 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
            (138 138
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
            (138 138
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
            (138 138
                 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
            (138 138
                 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
            (138 138
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
            (138 138
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
            (120 4 (:LINEAR MOD-BOUNDS-2))
            (120 4 (:LINEAR MOD-BOUNDS-1))
            (78 78
                (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
            (78 78 (:REWRITE |(< (- x) (- y))|))
            (73 73 (:REWRITE FOLD-CONSTS-IN-+))
            (70 70
                (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
            (62 62
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (62 62 (:REWRITE DEFAULT-*-1))
            (54 2 (:LINEAR MOD-BOUNDS-3))
            (32 8 (:REWRITE MOD-COMPLETION))
            (29 29 (:REWRITE |(< d (+ c x))|))
            (29 29 (:REWRITE |(< (+ c x) d)|))
            (27 27 (:REWRITE |(< 0 (- x))|))
            (27 27 (:REWRITE |(< (- x) 0)|))
            (25 25
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (25 25 (:REWRITE DEFAULT-UNARY-/))
            (24 24 (:REWRITE |(* c (* d x))|))
            (22 22 (:REWRITE |(equal (- x) (- y))|))
            (21 21
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
            (21 21
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
            (16 16 (:REWRITE REDUCE-INTEGERP-+))
            (16 16 (:REWRITE INTEGERP-MINUS-X))
            (12 12 (:REWRITE |(equal (- x) 0)|))
            (12 12 (:REWRITE |(equal (+ c x) d)|))
            (12 12 (:REWRITE |(< d (+ c x y))|))
            (12 12 (:REWRITE |(< (+ d x) (+ c y))|))
            (12 12 (:REWRITE |(< (+ c x) (+ d y))|))
            (12 12 (:REWRITE |(< (+ c x y) d)|))
            (11 11
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
            (10 10 (:REWRITE |(equal (+ c x y) d)|))
            (10 4 (:REWRITE MOD-ZERO . 2))
            (8 8
               (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
            (8 8 (:REWRITE |(integerp (* c x))|))
            (7 7 (:REWRITE |(equal (+ d x) (+ c y))|))
            (7 7 (:REWRITE |(equal (+ c x) (+ d y))|))
            (4 4 (:REWRITE MOD-X-Y-=-X . 2))
            (4 4 (:REWRITE |(- (* c x))|)))
(REWRITE-FLOOR-X*Y-Z-RIGHT-WEAK
     (276 4 (:LINEAR FLOOR-BOUNDS-3))
     (276 4 (:LINEAR FLOOR-BOUNDS-2))
     (161 23 (:REWRITE DEFAULT-UNARY-/))
     (151 7 (:REWRITE FLOOR-ZERO . 2))
     (144 32 (:META META-INTEGERP-CORRECT))
     (125 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (93 7 (:REWRITE FLOOR-ZERO . 4))
     (93 7 (:REWRITE FLOOR-ZERO . 3))
     (90 30 (:REWRITE DEFAULT-*-2))
     (52 52 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (52 52 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (52 52
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (48 3 (:REWRITE |(equal (* x y) 0)|))
     (36 36 (:REWRITE |(equal (- x) 0)|))
     (36 36 (:REWRITE |(equal (- x) (- y))|))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (33 33 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (33 33
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (33 33
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 32 (:REWRITE REDUCE-INTEGERP-+))
     (32 32 (:REWRITE INTEGERP-MINUS-X))
     (30 30
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (30 30 (:REWRITE DEFAULT-*-1))
     (27 3 (:REWRITE DEFAULT-+-2))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (21 3 (:REWRITE |(equal (/ x) 0)|))
     (19 7 (:REWRITE FLOOR-COMPLETION))
     (15 15 (:REWRITE |(* c (* d x))|))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14 14
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (14 14
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (14 14 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE |(integerp (* c x))|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (7 7 (:REWRITE |(< 0 (- x))|))
     (7 7 (:REWRITE |(< (- x) 0)|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-+-1)))
(REWRITE-MOD-X*Y-Z-RIGHT
     (226 4 (:LINEAR FLOOR-BOUNDS-3))
     (226 4 (:LINEAR FLOOR-BOUNDS-2))
     (214 14 (:REWRITE DEFAULT-+-2))
     (170 38 (:REWRITE DEFAULT-*-2))
     (120 9 (:REWRITE FLOOR-ZERO . 4))
     (120 9 (:REWRITE FLOOR-ZERO . 3))
     (110 110 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (110 110 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (110 110
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (96 32 (:META META-INTEGERP-CORRECT))
     (94 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (79 9 (:REWRITE FLOOR-ZERO . 2))
     (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (59 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (52 52 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (52 52
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (52 52
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (52 52 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (52 52 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (52 52
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (52 52
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (52 52 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (44 2 (:REWRITE MOD-ZERO . 2))
     (38 38
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (38 38 (:REWRITE DEFAULT-*-1))
     (34 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (32 32 (:REWRITE REDUCE-INTEGERP-+))
     (32 32 (:REWRITE INTEGERP-MINUS-X))
     (32 26 (:REWRITE DEFAULT-UNARY-/))
     (27 2 (:REWRITE MOD-X-Y-=-X . 4))
     (27 2 (:REWRITE MOD-X-Y-=-X . 3))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (26 26
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (26 26
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (26 14 (:REWRITE DEFAULT-+-1))
     (25 9 (:REWRITE FLOOR-COMPLETION))
     (25 2 (:REWRITE MOD-ZERO . 3))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 24 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-<-1))
     (24 24 (:REWRITE |(equal (- x) (- y))|))
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (22 22 (:REWRITE |(* c (* d x))|))
     (17 17 (:REWRITE |(equal (- x) 0)|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 2 (:REWRITE |(equal (/ x) 0)|))
     (12 12 (:REWRITE |(+ c (+ d x))|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (11 11 (:REWRITE |(< 0 (- x))|))
     (11 11 (:REWRITE |(< (- x) 0)|))
     (8 8 (:REWRITE |(integerp (* c x))|))
     (8 4 (:REWRITE MOD-COMPLETION))
     (7 7 (:REWRITE |(- (* c x))|))
     (5 5 (:REWRITE |(equal (+ c x) d)|))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (2 2 (:REWRITE MOD-X-Y-=-X . 2))
     (2 2 (:REWRITE |(equal (+ d x) (+ c y))|))
     (2 2 (:REWRITE |(equal (+ c x) (+ d y))|))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(equal (+ c x y) d)|)))
(FLOOR-MINUS-WEAK (301 21 (:REWRITE FLOOR-ZERO . 4))
                  (301 21 (:REWRITE FLOOR-ZERO . 3))
                  (190 190 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (190 190 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (190 190
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (189 35 (:REWRITE |(< 0 (- x))|))
                  (189 35 (:REWRITE |(< (- x) 0)|))
                  (165 27 (:REWRITE DEFAULT-UNARY-/))
                  (147 21 (:REWRITE FLOOR-ZERO . 2))
                  (144 48
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (94 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (70 70
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                  (70 70
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                  (70 70 (:REWRITE |(< (- x) (- y))|))
                  (69 9 (:REWRITE DEFAULT-+-2))
                  (51 3 (:REWRITE |(equal (+ c x) d)|))
                  (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (48 48 (:REWRITE |(equal (- x) (- y))|))
                  (48 24 (:REWRITE DEFAULT-UNARY-MINUS))
                  (45 45
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                  (45 45 (:REWRITE |(equal (- x) 0)|))
                  (42 42 (:REWRITE SIMPLIFY-SUMS-<))
                  (42 42
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                  (42 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                  (42 42 (:REWRITE DEFAULT-<-2))
                  (42 42 (:REWRITE DEFAULT-<-1))
                  (27 27
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                  (27 27
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (27 27 (:REWRITE DEFAULT-*-2))
                  (27 27 (:REWRITE DEFAULT-*-1))
                  (21 21
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                  (21 21
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                  (21 21 (:REWRITE FLOOR-COMPLETION))
                  (21 9 (:REWRITE DEFAULT-+-1))
                  (20 20 (:REWRITE |(- (* c x))|))
                  (13 1 (:REWRITE |(equal (+ c x y) d)|))
                  (9 9
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (1 1 (:REWRITE REDUCE-INTEGERP-+))
                  (1 1 (:REWRITE INTEGERP-MINUS-X))
                  (1 1 (:REWRITE FOLD-CONSTS-IN-+))
                  (1 1 (:REWRITE |(integerp (* c x))|))
                  (1 1 (:META META-INTEGERP-CORRECT)))
(FLOOR-MINUS-2 (231 21 (:REWRITE FLOOR-ZERO . 4))
               (231 21 (:REWRITE FLOOR-ZERO . 3))
               (190 190 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (190 190 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (190 190
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (189 21 (:REWRITE FLOOR-ZERO . 2))
               (165 27 (:REWRITE DEFAULT-UNARY-/))
               (144 48
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (143 59 (:REWRITE |(equal (- x) 0)|))
               (94 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (69 9 (:REWRITE DEFAULT-+-2))
               (68 44 (:REWRITE DEFAULT-UNARY-MINUS))
               (62 62 (:REWRITE |(equal (- x) (- y))|))
               (51 3 (:REWRITE |(equal (+ c x) d)|))
               (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (45 45
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (42 42 (:REWRITE SIMPLIFY-SUMS-<))
               (42 42
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (42 42
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
               (42 42
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
               (42 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (42 42 (:REWRITE DEFAULT-<-2))
               (42 42 (:REWRITE DEFAULT-<-1))
               (42 42 (:REWRITE |(< (- x) (- y))|))
               (27 27
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
               (27 27
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (27 27 (:REWRITE DEFAULT-*-2))
               (27 27 (:REWRITE DEFAULT-*-1))
               (21 21
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (21 21
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (21 21 (:REWRITE FLOOR-MINUS-WEAK))
               (21 21 (:REWRITE FLOOR-COMPLETION))
               (21 21 (:REWRITE |(< 0 (- x))|))
               (21 21 (:REWRITE |(< (- x) 0)|))
               (21 9 (:REWRITE DEFAULT-+-1))
               (20 20 (:REWRITE |(- (* c x))|))
               (13 1 (:REWRITE |(equal (+ c x y) d)|))
               (9 9
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (1 1 (:REWRITE REDUCE-INTEGERP-+))
               (1 1 (:REWRITE INTEGERP-MINUS-X))
               (1 1 (:REWRITE FOLD-CONSTS-IN-+))
               (1 1 (:REWRITE |(integerp (* c x))|))
               (1 1 (:META META-INTEGERP-CORRECT)))
(MOD-NEG (203 203 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
         (203 203 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
         (203 203 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
         (203 203
              (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
         (158 14 (:REWRITE DEFAULT-+-2))
         (143 143
              (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
         (143 143
              (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
         (143 143
              (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
         (118 22
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (101 13 (:REWRITE DEFAULT-UNARY-MINUS))
         (97 13 (:REWRITE DEFAULT-*-2))
         (77 7 (:REWRITE FLOOR-ZERO . 4))
         (77 7 (:REWRITE FLOOR-ZERO . 3))
         (51 51
             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
         (51 51
             (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
         (51 51
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
         (51 51
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
         (48 48 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
         (48 48 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
         (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD))
         (27 2 (:REWRITE MOD-X-Y-=-X . 4))
         (27 2 (:REWRITE MOD-X-Y-=-X . 3))
         (26 26
             (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
         (25 7 (:REWRITE FLOOR-ZERO . 2))
         (23 23 (:REWRITE |(equal (- x) (- y))|))
         (22 16 (:REWRITE |(equal (- x) 0)|))
         (21 10 (:REWRITE |(< 0 (- x))|))
         (21 10 (:REWRITE |(< (- x) 0)|))
         (20 20
             (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
         (20 20
             (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
         (20 20 (:REWRITE |(< (- x) (- y))|))
         (18 18 (:REWRITE SIMPLIFY-SUMS-<))
         (18 18
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
         (18 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
         (18 18 (:REWRITE DEFAULT-<-2))
         (18 18 (:REWRITE DEFAULT-<-1))
         (17 2 (:REWRITE MOD-ZERO . 3))
         (14 14
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
         (14 14
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (14 14 (:REWRITE DEFAULT-+-1))
         (14 2 (:REWRITE MOD-ZERO . 2))
         (13 13
             (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
         (13 13 (:REWRITE DEFAULT-*-1))
         (12 12 (:REWRITE |(+ c (+ d x))|))
         (12 6 (:REWRITE DEFAULT-UNARY-/))
         (9 9
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
         (9 9
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
         (8 8 (:REWRITE FLOOR-MINUS-2))
         (8 8 (:REWRITE ARITH-NORMALIZE-ADDENDS))
         (8 8 (:LINEAR FLOOR-BOUNDS-3))
         (7 7 (:REWRITE FLOOR-COMPLETION))
         (7 7 (:META META-INTEGERP-CORRECT))
         (6 6 (:REWRITE REDUCE-INTEGERP-+))
         (6 6
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
         (6 6 (:REWRITE |(integerp (* c x))|))
         (6 6 (:REWRITE |(- (* c x))|))
         (4 4 (:REWRITE MOD-COMPLETION))
         (3 3 (:REWRITE FOLD-CONSTS-IN-+))
         (3 3 (:REWRITE |(equal (+ c x) d)|))
         (2 2 (:REWRITE MOD-X-Y-=-X . 2))
         (1 1 (:REWRITE |(equal (+ d x) (+ c y))|))
         (1 1 (:REWRITE |(equal (+ c x) (+ d y))|))
         (1 1 (:REWRITE |(equal (+ c x y) d)|)))
(MOD-MINUS-2 (203 203 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
             (203 203 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
             (203 203 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
             (203 203
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
             (158 14 (:REWRITE DEFAULT-+-2))
             (142 142
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
             (142 142
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
             (142 142
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
             (118 22
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (103 15 (:REWRITE DEFAULT-UNARY-MINUS))
             (97 13 (:REWRITE DEFAULT-*-2))
             (77 7 (:REWRITE FLOOR-ZERO . 4))
             (77 7 (:REWRITE FLOOR-ZERO . 3))
             (51 51
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
             (51 51
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
             (51 51
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
             (51 51
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
             (48 48 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
             (48 48 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
             (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD))
             (26 26
                 (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
             (25 7 (:REWRITE FLOOR-ZERO . 2))
             (23 23 (:REWRITE |(equal (- x) (- y))|))
             (22 16 (:REWRITE |(equal (- x) 0)|))
             (22 2 (:REWRITE MOD-X-Y-=-X . 4))
             (22 2 (:REWRITE MOD-X-Y-=-X . 3))
             (18 18 (:REWRITE SIMPLIFY-SUMS-<))
             (18 18
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
             (18 18
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
             (18 18
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
             (18 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
             (18 18 (:REWRITE DEFAULT-<-2))
             (18 18 (:REWRITE DEFAULT-<-1))
             (18 18 (:REWRITE |(< (- x) (- y))|))
             (17 2 (:REWRITE MOD-ZERO . 2))
             (14 14
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
             (14 14
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (14 14 (:REWRITE DEFAULT-+-1))
             (14 2 (:REWRITE MOD-ZERO . 3))
             (13 13
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (13 13 (:REWRITE DEFAULT-*-1))
             (12 6 (:REWRITE DEFAULT-UNARY-/))
             (10 10 (:REWRITE |(+ c (+ d x))|))
             (9 9
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
             (9 9
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
             (9 9 (:REWRITE |(< 0 (- x))|))
             (9 9 (:REWRITE |(< (- x) 0)|))
             (8 8 (:REWRITE ARITH-NORMALIZE-ADDENDS))
             (8 8 (:LINEAR FLOOR-BOUNDS-3))
             (7 7 (:REWRITE FLOOR-MINUS-WEAK))
             (7 7 (:REWRITE FLOOR-COMPLETION))
             (7 7 (:META META-INTEGERP-CORRECT))
             (6 6 (:REWRITE REDUCE-INTEGERP-+))
             (6 6
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
             (6 6 (:REWRITE |(integerp (* c x))|))
             (6 6 (:REWRITE |(- (* c x))|))
             (4 4 (:REWRITE MOD-COMPLETION))
             (3 3 (:REWRITE |(equal (+ c x) d)|))
             (2 2 (:REWRITE MOD-X-Y-=-X . 2))
             (2 2 (:REWRITE MOD-NEG))
             (2 2 (:REWRITE FOLD-CONSTS-IN-+))
             (1 1 (:REWRITE |(equal (+ d x) (+ c y))|))
             (1 1 (:REWRITE |(equal (+ c x) (+ d y))|))
             (1 1 (:REWRITE |(equal (+ c x y) d)|)))
(REWRITE-FLOOR-MOD-WEAK
     (3969 1065 (:REWRITE DEFAULT-+-2))
     (2699 2699
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1650 1154 (:REWRITE DEFAULT-*-2))
     (1571 1065 (:REWRITE DEFAULT-+-1))
     (1315 1255
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1255 1255
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1154 1154
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1154 1154 (:REWRITE DEFAULT-*-1))
     (1145 1145
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1145 1145
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1145 1145
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1145 1145
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1145 1145
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1142 1142
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (1142 1142
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (1142 1142
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (1142 1142
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (1123 1123
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (1065 1065
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (845 181
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (683 365 (:REWRITE DEFAULT-UNARY-/))
     (628 628
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (628 628
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (628 628
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (628 628
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (527 527
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (499 499 (:REWRITE |(< (- x) (- y))|))
     (490 392 (:REWRITE DEFAULT-<-2))
     (442 392 (:REWRITE DEFAULT-<-1))
     (440 152
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (365 365
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (346 100 (:META META-INTEGERP-CORRECT))
     (340 340 (:REWRITE FOLD-CONSTS-IN-+))
     (264 264 (:REWRITE |(* c (* d x))|))
     (260 102 (:REWRITE FLOOR-ZERO . 2))
     (248 248 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (248 248 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (248 248
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (248 248
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (248 248
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (248 248
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (248 248
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (248 248
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (248 248 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (193 193 (:REWRITE |(< (- x) 0)|))
     (189 189 (:REWRITE |(< 0 (- x))|))
     (181 181 (:REWRITE |(equal (- x) (- y))|))
     (157 157 (:REWRITE |(< (+ c x) d)|))
     (154 104 (:REWRITE FLOOR-MINUS-WEAK))
     (154 104 (:REWRITE FLOOR-MINUS-2))
     (152 152 (:REWRITE |(equal (- x) 0)|))
     (150 100 (:REWRITE FLOOR-COMPLETION))
     (129 109 (:REWRITE DEFAULT-UNARY-MINUS))
     (127 127 (:REWRITE |(< d (+ c x))|))
     (100 100 (:REWRITE INTEGERP-MINUS-X))
     (84 84 (:REWRITE |(< (+ c x y) d)|))
     (62 62 (:REWRITE |(< d (+ c x y))|))
     (57 57 (:REWRITE |(integerp (* c x))|))
     (55 5 (:REWRITE MOD-X-Y-=-X . 4))
     (55 5 (:REWRITE MOD-X-Y-=-X . 3))
     (46 46 (:REWRITE |arith (* c (* d x))|))
     (36 36 (:REWRITE |(equal (+ c x) d)|))
     (35 5 (:REWRITE MOD-ZERO . 3))
     (35 5 (:REWRITE MOD-ZERO . 2))
     (28 28 (:LINEAR MOD-BOUNDS-2))
     (28 28 (:LINEAR MOD-BOUNDS-1))
     (26 26 (:REWRITE |arith (* (- x) y)|))
     (18 18 (:REWRITE |arith (- (* c x))|))
     (14 14 (:REWRITE |(< (+ d x) (+ c y))|))
     (14 14 (:REWRITE |(< (+ c x) (+ d y))|))
     (14 14 (:LINEAR MOD-BOUNDS-3))
     (12 12 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (10 10 (:REWRITE MOD-COMPLETION))
     (10 10
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (5 5 (:REWRITE MOD-X-Y-=-X . 2))
     (5 5 (:REWRITE MOD-POSITIVE . 3))
     (5 5 (:REWRITE MOD-POSITIVE . 2))
     (5 5 (:REWRITE MOD-POSITIVE . 1))
     (5 5 (:REWRITE MOD-NONPOSITIVE))
     (5 5 (:REWRITE MOD-NONNEGATIVE))
     (5 5 (:REWRITE MOD-NEGATIVE . 3))
     (5 5 (:REWRITE MOD-NEGATIVE . 2))
     (5 5 (:REWRITE MOD-NEGATIVE . 1))
     (5 5 (:REWRITE MOD-NEG))
     (5 5 (:REWRITE MOD-MINUS-2))
     (4 4 (:REWRITE |(equal (+ c x y) d)|))
     (1 1 (:REWRITE |(- (* c x))|)))
(REWRITE-MOD-MOD-WEAK
     (9583 9583
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5251 3379
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (5235 3379
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (4738 3370 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (4500 88 (:LINEAR MOD-BOUNDS-3))
     (4069 1417 (:REWRITE DEFAULT-+-2))
     (3379 3379
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (3379 3379
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (3170 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2992 1662 (:REWRITE DEFAULT-*-2))
     (2025 1417 (:REWRITE DEFAULT-+-1))
     (1998 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1688 176 (:LINEAR MOD-BOUNDS-2))
     (1688 176 (:LINEAR MOD-BOUNDS-1))
     (1662 1662
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1662 1662 (:REWRITE DEFAULT-*-1))
     (1650 1650
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (1650 1650
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (1417 1417
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1208 236
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1208 236
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1116 268 (:META META-INTEGERP-CORRECT))
     (1008 1008
           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (957 957 (:REWRITE |(< (- x) (- y))|))
     (943 741 (:REWRITE DEFAULT-<-2))
     (895 741 (:REWRITE DEFAULT-<-1))
     (838 838
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (586 514 (:REWRITE DEFAULT-UNARY-/))
     (514 514
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (492 492 (:REWRITE FOLD-CONSTS-IN-+))
     (457 217
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (375 221 (:REWRITE MOD-NEG))
     (375 221 (:REWRITE MOD-MINUS-2))
     (339 339 (:REWRITE |(< (- x) 0)|))
     (338 338 (:REWRITE |(< 0 (- x))|))
     (268 268 (:REWRITE INTEGERP-MINUS-X))
     (258 258 (:REWRITE |(* c (* d x))|))
     (236 236 (:REWRITE |(equal (- x) (- y))|))
     (232 78 (:REWRITE MOD-COMPLETION))
     (217 217 (:REWRITE |(equal (- x) 0)|))
     (216 216 (:REWRITE DEFAULT-UNARY-MINUS))
     (188 188 (:REWRITE |(< (+ c x) d)|))
     (176 176 (:REWRITE |(integerp (* c x))|))
     (124 124 (:REWRITE |(< d (+ c x))|))
     (103 103 (:REWRITE MOD-X-Y-=-X . 2))
     (88 8 (:REWRITE FLOOR-ZERO . 4))
     (88 8 (:REWRITE FLOOR-ZERO . 3))
     (84 3 (:LINEAR FLOOR-BOUNDS-3))
     (84 3 (:LINEAR FLOOR-BOUNDS-2))
     (80 80 (:REWRITE |(< (+ c x y) d)|))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (56 8 (:REWRITE FLOOR-ZERO . 2))
     (42 42 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (42 42 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (42 42 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (42 42
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (36 36 (:REWRITE |(< d (+ c x y))|))
     (32 32
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (28 28 (:REWRITE |(< (+ d x) (+ c y))|))
     (28 28 (:REWRITE |(< (+ c x) (+ d y))|))
     (24 24 (:REWRITE |(equal (+ c x) d)|))
     (11 11 (:REWRITE MOD-ZERO . 1))
     (11 11 (:REWRITE MOD-POSITIVE . 3))
     (11 11 (:REWRITE MOD-POSITIVE . 2))
     (11 11 (:REWRITE MOD-POSITIVE . 1))
     (11 11 (:REWRITE MOD-NONPOSITIVE))
     (11 11 (:REWRITE MOD-NONNEGATIVE))
     (11 11 (:REWRITE MOD-NEGATIVE . 3))
     (11 11 (:REWRITE MOD-NEGATIVE . 2))
     (11 11 (:REWRITE MOD-NEGATIVE . 1))
     (8 8 (:REWRITE FLOOR-MINUS-WEAK))
     (8 8 (:REWRITE FLOOR-MINUS-2))
     (8 8 (:REWRITE FLOOR-COMPLETION))
     (8 8 (:REWRITE |(equal (+ c x y) d)|)))
(MOD-+-CANCEL-0-FN-1 (370 20 (:DEFINITION INTEGER-ABS))
                     (308 102 (:REWRITE DEFAULT-+-2))
                     (190 10 (:REWRITE |(+ (if a b c) x)|))
                     (133 13 (:DEFINITION LENGTH))
                     (130 102 (:REWRITE DEFAULT-+-1))
                     (110 110 (:REWRITE DEFAULT-CDR))
                     (110 10 (:REWRITE NUMERATOR-NEGATIVE))
                     (102 102
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (98 14 (:DEFINITION LEN))
                     (73 73 (:REWRITE DEFAULT-CAR))
                     (64 22 (:REWRITE DEFAULT-UNARY-MINUS))
                     (54 38
                         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                     (45 27
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                     (45 27 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                     (40 40
                         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                     (40 40
                         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                     (40 40
                         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                     (40 40
                         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                     (38 38 (:TYPE-PRESCRIPTION LEN))
                     (38 38
                         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                     (37 37 (:REWRITE |(< (- x) (- y))|))
                     (34 34 (:REWRITE FOLD-CONSTS-IN-+))
                     (34 26 (:REWRITE DEFAULT-<-2))
                     (31 26 (:REWRITE DEFAULT-<-1))
                     (30 30 (:REWRITE |(< (- x) 0)|))
                     (29 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (29 24
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (29 24
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (24 24 (:REWRITE |(equal (- x) (- y))|))
                     (20 20
                         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                     (14 3 (:REWRITE |(< d (+ c x))|))
                     (11 11 (:REWRITE DEFAULT-COERCE-2))
                     (11 11 (:REWRITE DEFAULT-COERCE-1))
                     (10 10 (:REWRITE REDUCE-INTEGERP-+))
                     (10 10 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                     (10 10
                         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                     (10 10 (:REWRITE INTEGERP-MINUS-X))
                     (10 10 (:REWRITE DEFAULT-REALPART))
                     (10 10 (:REWRITE DEFAULT-NUMERATOR))
                     (10 10 (:REWRITE DEFAULT-IMAGPART))
                     (10 10 (:REWRITE DEFAULT-DENOMINATOR))
                     (10 10 (:META META-INTEGERP-CORRECT))
                     (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
                     (6 6
                        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
                     (6 3 (:REWRITE |(< d (+ c x y))|))
                     (6 1 (:REWRITE |(< (+ d x) (+ c y))|))
                     (3 1 (:DEFINITION SYMBOL-LISTP))
                     (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
                     (1 1
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                     (1 1 (:REWRITE |(< 0 (- x))|)))
(MOD-+-CANCEL-0-FN)
(LOCAL-MOD-+-CANCEL-0
     (1170 362 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (895 895
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (895 895
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (893 893
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (774 362
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (758 362
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (654 42 (:REWRITE |(* (+ x y) z)|))
     (428 13 (:LINEAR MOD-BOUNDS-3))
     (362 362
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (362 362
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (362 362 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (320 320 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (320 320 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (320 320
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (305 73 (:REWRITE DEFAULT-+-2))
     (272 8 (:LINEAR FLOOR-BOUNDS-3))
     (272 8 (:LINEAR FLOOR-BOUNDS-2))
     (257 59
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (250 106 (:REWRITE DEFAULT-*-2))
     (225 73 (:REWRITE DEFAULT-+-1))
     (224 30 (:REWRITE MOD-ZERO . 3))
     (146 12 (:REWRITE FLOOR-ZERO . 4))
     (146 12 (:REWRITE FLOOR-ZERO . 3))
     (120 120 (:REWRITE SIMPLIFY-SUMS-<))
     (120 120
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (120 120
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (120 120
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (120 120
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (120 120 (:REWRITE DEFAULT-<-2))
     (120 120 (:REWRITE DEFAULT-<-1))
     (120 120 (:REWRITE |(< (- x) (- y))|))
     (108 108 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (106 106
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (106 106 (:REWRITE DEFAULT-*-1))
     (84 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (73 73
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (70 70 (:REWRITE MOD-NEG))
     (70 70 (:REWRITE MOD-MINUS-2))
     (61 61
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (61 61 (:REWRITE |(< 0 (- x))|))
     (59 59 (:REWRITE |(equal (- x) (- y))|))
     (56 56
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (56 56 (:REWRITE DEFAULT-UNARY-/))
     (54 54 (:REWRITE |arith (* (- x) y)|))
     (53 53
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (53 53 (:REWRITE |(< (- x) 0)|))
     (52 52 (:REWRITE REDUCE-INTEGERP-+))
     (52 52 (:REWRITE INTEGERP-MINUS-X))
     (52 52 (:META META-INTEGERP-CORRECT))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (43 43 (:REWRITE |(equal (- x) 0)|))
     (36 36 (:REWRITE |arith (* c (* d x))|))
     (36 36
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (34 34 (:REWRITE MOD-COMPLETION))
     (30 30 (:REWRITE MOD-X-Y-=-X . 2))
     (30 30 (:REWRITE |(< d (+ c x))|))
     (26 26 (:REWRITE |(< (+ c x) d)|))
     (20 20 (:REWRITE |(+ c (+ d x))|))
     (19 19 (:REWRITE |(equal (+ c x) d)|))
     (16 16 (:REWRITE |(integerp (* c x))|))
     (12 12 (:REWRITE FLOOR-ZERO . 2))
     (12 12 (:REWRITE FLOOR-MINUS-WEAK))
     (12 12 (:REWRITE FLOOR-MINUS-2))
     (12 12 (:REWRITE FLOOR-COMPLETION))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(- (* c x))|))
     (4 4 (:REWRITE |(* 0 x)|))
     (2 2 (:REWRITE |arith (- (* c x))|))
     (2 2 (:REWRITE |(equal (+ d x) (+ c y))|))
     (2 2 (:REWRITE |(equal (+ c x) (+ d y))|))
     (2 2 (:REWRITE |(equal (+ c x y) d)|)))
(MOD-+-CANCEL-0-WEAK
     (508 336 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (505 109
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (406 35 (:REWRITE REDUCE-INTEGERP-+))
     (336 336
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (336 336
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (336 336
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (336 336
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (336 336
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (336 336
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (336 336 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (182 42 (:REWRITE INTEGERP-MINUS-X))
     (141 141
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (141 141
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (141 141
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (125 125
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (125 125
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (125 125
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (125 125
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (116 36 (:REWRITE DEFAULT-UNARY-MINUS))
     (109 109
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (109 109
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (109 109 (:REWRITE |(< (- x) (- y))|))
     (103 103
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (87 87 (:REWRITE SIMPLIFY-SUMS-<))
     (87 87 (:REWRITE DEFAULT-<-2))
     (87 87 (:REWRITE DEFAULT-<-1))
     (78 26 (:REWRITE DEFAULT-+-2))
     (78 26 (:REWRITE DEFAULT-+-1))
     (72 62
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (62 62 (:REWRITE |(equal (- x) (- y))|))
     (58 58 (:REWRITE MOD-COMPLETION))
     (52 42 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (51 51
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (51 51 (:REWRITE DEFAULT-*-2))
     (51 51 (:REWRITE DEFAULT-*-1))
     (51 51 (:REWRITE |(equal (- x) 0)|))
     (43 43 (:REWRITE |(+ c (+ d x))|))
     (42 42 (:META META-INTEGERP-CORRECT))
     (39 39 (:REWRITE MOD-NEG))
     (39 39 (:REWRITE MOD-MINUS-2))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (38 38 (:REWRITE DEFAULT-UNARY-/))
     (37 37 (:REWRITE MOD-X-Y-=-X . 2))
     (37 37 (:REWRITE |(< 0 (- x))|))
     (37 37 (:REWRITE |(< (- x) 0)|))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (25 25 (:REWRITE |(integerp (* c x))|))
     (20 20 (:REWRITE |(equal (+ c x) d)|))
     (20 20 (:REWRITE |(- (* c x))|))
     (11 11 (:REWRITE |(< d (+ c x))|))
     (11 11 (:REWRITE |(< (+ c x) d)|))
     (10 10
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT)))
(FACTORS-CCC (629 34 (:DEFINITION INTEGER-ABS))
             (549 49 (:DEFINITION LENGTH))
             (520 186 (:REWRITE DEFAULT-+-2))
             (442 62 (:DEFINITION LEN))
             (355 355 (:TYPE-PRESCRIPTION LEN))
             (323 17 (:REWRITE |(+ (if a b c) x)|))
             (226 186 (:REWRITE DEFAULT-+-1))
             (187 17 (:REWRITE NUMERATOR-NEGATIVE))
             (186 186
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (136 77 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (136 77
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (136 77
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (106 36 (:REWRITE DEFAULT-UNARY-MINUS))
             (77 77 (:REWRITE |(equal (- x) (- y))|))
             (77 61
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
             (68 68
                 (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
             (68 68
                 (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
             (68 68
                 (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
             (68 68
                 (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
             (62 43
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
             (62 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
             (61 61
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
             (60 60 (:REWRITE |(< (- x) (- y))|))
             (52 42 (:REWRITE DEFAULT-<-2))
             (51 51 (:REWRITE |(< (- x) 0)|))
             (47 42 (:REWRITE DEFAULT-<-1))
             (43 43 (:REWRITE FOLD-CONSTS-IN-+))
             (35 35
                 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
             (34 34
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
             (33 11 (:DEFINITION SYMBOL-LISTP))
             (30 30
                 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
             (29 29 (:REWRITE DEFAULT-COERCE-2))
             (29 29 (:REWRITE DEFAULT-COERCE-1))
             (17 17 (:REWRITE REDUCE-INTEGERP-+))
             (17 17 (:REWRITE INTEGERP==>NUMERATOR-=-X))
             (17 17
                 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
             (17 17 (:REWRITE INTEGERP-MINUS-X))
             (17 17 (:REWRITE DEFAULT-REALPART))
             (17 17 (:REWRITE DEFAULT-NUMERATOR))
             (17 17 (:REWRITE DEFAULT-IMAGPART))
             (17 17 (:REWRITE DEFAULT-DENOMINATOR))
             (17 17 (:META META-INTEGERP-CORRECT))
             (11 11 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
             (6 3 (:REWRITE |(< d (+ c x y))|))
             (4 4
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
             (4 4 (:REWRITE |(equal (- x) 0)|))
             (4 2 (:REWRITE |(equal (+ c x) d)|))
             (2 2
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
             (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
             (2 2 (:REWRITE |(< 0 (- x))|)))
(NON-ZERO-INTERSECTION-EQUAL
     (7 7
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 4 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE DEFAULT-CDR)))
(MAKE-PRODUCT-CCC (555 30 (:DEFINITION INTEGER-ABS))
                  (381 124 (:REWRITE DEFAULT-+-2))
                  (285 15 (:REWRITE |(+ (if a b c) x)|))
                  (165 15 (:REWRITE NUMERATOR-NEGATIVE))
                  (163 124 (:REWRITE DEFAULT-+-1))
                  (150 15 (:DEFINITION LENGTH))
                  (124 124
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (105 15 (:DEFINITION LEN))
                  (98 34 (:REWRITE DEFAULT-UNARY-MINUS))
                  (71 55
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                  (60 60
                      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                  (60 60
                      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                  (60 60
                      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                  (60 60
                      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                  (57 38
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                  (57 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                  (55 55
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                  (53 53 (:REWRITE DEFAULT-CDR))
                  (53 53 (:REWRITE |(< (- x) (- y))|))
                  (45 45 (:REWRITE |(< (- x) 0)|))
                  (42 36 (:REWRITE DEFAULT-<-2))
                  (41 36 (:REWRITE DEFAULT-<-1))
                  (40 40 (:REWRITE FOLD-CONSTS-IN-+))
                  (30 30
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                  (18 18 (:REWRITE DEFAULT-CAR))
                  (15 15 (:TYPE-PRESCRIPTION LEN))
                  (15 15 (:REWRITE REDUCE-INTEGERP-+))
                  (15 15 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                  (15 15
                      (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                  (15 15 (:REWRITE INTEGERP-MINUS-X))
                  (15 15 (:REWRITE DEFAULT-REALPART))
                  (15 15 (:REWRITE DEFAULT-NUMERATOR))
                  (15 15 (:REWRITE DEFAULT-IMAGPART))
                  (15 15 (:REWRITE DEFAULT-DENOMINATOR))
                  (15 15 (:REWRITE DEFAULT-COERCE-2))
                  (15 15 (:REWRITE DEFAULT-COERCE-1))
                  (15 15 (:META META-INTEGERP-CORRECT))
                  (8 2 (:REWRITE |(< (+ d x) (+ c y))|))
                  (6 3 (:REWRITE |(< d (+ c x y))|))
                  (1 1 (:REWRITE |(< (+ c x) d)|)))
(FIND-COMMON-FACTORS
     (1232 176 (:DEFINITION LEN))
     (910 882 (:REWRITE DEFAULT-CDR))
     (759 731 (:REWRITE DEFAULT-CAR))
     (496 273 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (496 273
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (496 273
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (352 176 (:REWRITE DEFAULT-+-2))
     (273 273 (:REWRITE |(equal (- x) (- y))|))
     (176 176
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (176 176 (:REWRITE NORMALIZE-ADDENDS))
     (176 176 (:REWRITE DEFAULT-+-1))
     (133 133
          (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (132 44 (:DEFINITION SYMBOL-LISTP))
     (126 42
          (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (118 118
          (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (72 1
         (:DEFINITION NON-ZERO-INTERSECTION-EQUAL))
     (44 44 (:REWRITE DEFAULT-COERCE-2))
     (44 44 (:REWRITE DEFAULT-COERCE-1))
     (33 1
         (:DEFINITION PROVEABLY-NON-ZERO-RATIONAL))
     (23 1 (:DEFINITION MEMBER-EQUAL))
     (10 2 (:DEFINITION PROVEABLY-NON-ZERO1))
     (4 1 (:DEFINITION RATIONAL-CONSTANT-P))
     (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL)))
(FLOOR-CANCEL-*-WEAK (282 258
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                     (258 258
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (258 258
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (258 258
                          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (241 7 (:REWRITE FLOOR-ZERO . 4))
                     (241 7 (:REWRITE FLOOR-ZERO . 3))
                     (190 4 (:LINEAR FLOOR-BOUNDS-3))
                     (190 4 (:LINEAR FLOOR-BOUNDS-2))
                     (189 7 (:REWRITE FLOOR-ZERO . 2))
                     (105 15 (:REWRITE DEFAULT-UNARY-/))
                     (52 52 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                     (52 52 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                     (52 52
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                     (52 4 (:REWRITE |(equal (* x y) 0)|))
                     (46 14 (:REWRITE SIMPLIFY-SUMS-<))
                     (46 14
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                     (46 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                     (39 7 (:REWRITE FLOOR-MINUS-WEAK))
                     (39 7 (:REWRITE FLOOR-MINUS-2))
                     (39 7 (:REWRITE FLOOR-COMPLETION))
                     (31 31
                         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (31 31 (:REWRITE DEFAULT-*-2))
                     (31 31 (:REWRITE DEFAULT-*-1))
                     (30 14 (:REWRITE DEFAULT-<-2))
                     (30 14 (:REWRITE DEFAULT-<-1))
                     (26 26
                         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                     (26 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (26 26
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (26 26
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (26 26 (:REWRITE |(equal (- x) 0)|))
                     (26 26 (:REWRITE |(equal (- x) (- y))|))
                     (24 24 (:REWRITE |(* c (* d x))|))
                     (15 15
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                     (15 3 (:REWRITE DEFAULT-+-2))
                     (14 14
                         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                     (14 14
                         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                     (14 14 (:REWRITE |(< (- x) (- y))|))
                     (8 8 (:REWRITE REDUCE-INTEGERP-+))
                     (8 8 (:REWRITE INTEGERP-MINUS-X))
                     (8 8 (:REWRITE |(integerp (* c x))|))
                     (8 8 (:META META-INTEGERP-CORRECT))
                     (7 7
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                     (7 7
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                     (7 7 (:REWRITE |(< 0 (- x))|))
                     (7 7 (:REWRITE |(< (- x) 0)|))
                     (4 4 (:REWRITE |(< 0 (* x y))|))
                     (4 4 (:REWRITE |(< (* x y) 0)|))
                     (3 3
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (3 3 (:REWRITE NORMALIZE-ADDENDS))
                     (3 3 (:REWRITE DEFAULT-+-1)))
(MOD-CANCEL-* (72 56 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (63 2 (:REWRITE MOD-X-Y-=-X . 4))
              (63 2 (:REWRITE MOD-X-Y-=-X . 3))
              (56 56 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
              (56 56
                  (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
              (56 56
                  (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (56 56 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
              (56 56 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
              (56 56
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
              (56 56
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
              (47 3 (:REWRITE DEFAULT-UNARY-MINUS))
              (47 3 (:REWRITE DEFAULT-+-2))
              (45 9 (:REWRITE DEFAULT-*-2))
              (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
              (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (43 2 (:REWRITE MOD-ZERO . 3))
              (39 2 (:REWRITE MOD-ZERO . 2))
              (26 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
              (22 2 (:REWRITE FLOOR-ZERO . 4))
              (22 2 (:REWRITE FLOOR-ZERO . 3))
              (16 8 (:REWRITE SIMPLIFY-SUMS-<))
              (16 8
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
              (16 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (14 2 (:REWRITE FLOOR-ZERO . 2))
              (14 2 (:REWRITE |(equal (* x y) 0)|))
              (12 8 (:REWRITE DEFAULT-<-2))
              (12 8 (:REWRITE DEFAULT-<-1))
              (12 4 (:REWRITE MOD-COMPLETION))
              (10 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
              (10 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
              (10 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
              (10 10
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
              (10 2 (:REWRITE MOD-NEG))
              (10 2 (:REWRITE MOD-MINUS-2))
              (9 9
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (9 9 (:REWRITE DEFAULT-*-1))
              (8 8
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
              (8 8
                 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
              (8 8 (:REWRITE |(< (- x) (- y))|))
              (8 8 (:REWRITE |(* c (* d x))|))
              (7 7
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (7 7
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (7 7
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (7 7 (:REWRITE |(equal (- x) 0)|))
              (7 7 (:REWRITE |(equal (- x) (- y))|))
              (7 3 (:REWRITE DEFAULT-+-1))
              (4 4
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (4 4
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (4 4 (:REWRITE |(< 0 (- x))|))
              (4 4 (:REWRITE |(< (- x) 0)|))
              (3 3
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (3 3
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (3 3 (:REWRITE NORMALIZE-ADDENDS))
              (3 3 (:REWRITE DEFAULT-UNARY-/))
              (3 3 (:REWRITE |(- (* c x))|))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
              (2 2 (:REWRITE MOD-X-Y-=-X . 2))
              (2 2 (:REWRITE FLOOR-MINUS-WEAK))
              (2 2 (:REWRITE FLOOR-MINUS-2))
              (2 2 (:REWRITE FLOOR-COMPLETION))
              (1 1 (:REWRITE |(< 0 (* x y))|))
              (1 1 (:REWRITE |(< (* x y) 0)|)))
(FIND-CANCELLING-ADDENDS
     (333 18 (:DEFINITION INTEGER-ABS))
     (298 106 (:REWRITE DEFAULT-+-2))
     (205 17 (:DEFINITION LENGTH))
     (171 9 (:REWRITE |(+ (if a b c) x)|))
     (165 165 (:REWRITE DEFAULT-CDR))
     (162 22 (:DEFINITION LEN))
     (129 106 (:REWRITE DEFAULT-+-1))
     (123 123 (:TYPE-PRESCRIPTION LEN))
     (108 108 (:REWRITE DEFAULT-CAR))
     (106 106
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (99 9 (:REWRITE NUMERATOR-NEGATIVE))
     (65 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (65 46
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (65 46
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (58 20 (:REWRITE DEFAULT-UNARY-MINUS))
     (51 35
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (46 46 (:REWRITE |(equal (- x) (- y))|))
     (41 25
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (41 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (36 36
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (36 36
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (36 36
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (36 36
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (35 35
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (34 34 (:REWRITE |(< (- x) (- y))|))
     (31 24 (:REWRITE DEFAULT-<-2))
     (29 24 (:REWRITE DEFAULT-<-1))
     (28 28 (:REWRITE FOLD-CONSTS-IN-+))
     (27 27 (:REWRITE |(< (- x) 0)|))
     (21 8 (:REWRITE |(< d (+ c x))|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (18 6
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (13 13
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (13 13 (:REWRITE DEFAULT-COERCE-2))
     (13 13 (:REWRITE DEFAULT-COERCE-1))
     (9 9
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (9 9 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:REWRITE DEFAULT-REALPART))
     (9 9 (:REWRITE DEFAULT-NUMERATOR))
     (9 9 (:REWRITE DEFAULT-IMAGPART))
     (9 9 (:REWRITE DEFAULT-DENOMINATOR))
     (9 9 (:META META-INTEGERP-CORRECT))
     (9 3 (:DEFINITION SYMBOL-LISTP))
     (6 3 (:REWRITE |(< d (+ c x y))|))
     (5 1 (:REWRITE |(< (+ d x) (+ c y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (4 4 (:REWRITE |(equal (- x) 0)|))
     (4 2 (:REWRITE |(equal (+ c x) d)|))
     (3 3 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1 (:REWRITE |(< 0 (- x))|)))
(CANCEL-FLOOR-+ (182 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (149 7 (:REWRITE FLOOR-ZERO . 4))
                (149 7 (:REWRITE FLOOR-ZERO . 3))
                (144 4 (:LINEAR FLOOR-BOUNDS-3))
                (144 4 (:LINEAR FLOOR-BOUNDS-2))
                (105 15 (:REWRITE DEFAULT-UNARY-/))
                (79 23 (:REWRITE NORMALIZE-ADDENDS))
                (75 15 (:REWRITE DEFAULT-+-2))
                (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (52 52 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (52 52 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (52 52
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (49 7 (:REWRITE FLOOR-ZERO . 2))
                (40 8 (:REWRITE BUBBLE-DOWN-+-BUBBLE-DOWN))
                (24 16 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
                (23 23
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (23 23 (:REWRITE DEFAULT-*-2))
                (23 23 (:REWRITE DEFAULT-*-1))
                (22 22
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (22 22
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (22 22
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (22 22
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (22 22
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (22 22
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (22 22 (:REWRITE |(equal (- x) 0)|))
                (22 22 (:REWRITE |(equal (- x) (- y))|))
                (22 22 (:REWRITE |(< (- x) (- y))|))
                (16 16 (:REWRITE |(- (- x))|))
                (16 16 (:REWRITE |(+ 0 x)|))
                (15 15
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (15 15
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (15 15 (:REWRITE DEFAULT-+-1))
                (14 14 (:REWRITE SIMPLIFY-SUMS-<))
                (14 14 (:REWRITE DEFAULT-<-2))
                (14 14 (:REWRITE DEFAULT-<-1))
                (12 12 (:REWRITE |(+ c (+ d x))|))
                (8 8 (:REWRITE REDUCE-INTEGERP-+))
                (8 8 (:REWRITE INTEGERP-MINUS-X))
                (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
                (8 8 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
                (8 8 (:REWRITE |(- (* c x))|))
                (8 8 (:REWRITE |(+ x (- x))|))
                (8 8 (:META META-INTEGERP-CORRECT))
                (7 7 (:REWRITE FLOOR-MINUS-WEAK))
                (7 7 (:REWRITE FLOOR-MINUS-2))
                (7 7 (:REWRITE FLOOR-COMPLETION))
                (7 7 (:REWRITE FLOOR-CANCEL-*-WEAK))
                (7 7 (:REWRITE |(< 0 (- x))|))
                (7 7 (:REWRITE |(< (- x) 0)|))
                (4 4
                   (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
                (4 4 (:REWRITE |(integerp (* c x))|))
                (4 4 (:REWRITE |(< d (+ c x))|))
                (4 4 (:REWRITE |(< (+ c x) d)|))
                (3 3
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (3 3
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(CANCEL-MOD-+ (1484 364 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
              (841 841
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (704 16 (:LINEAR MOD-BOUNDS-3))
              (436 364
                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
              (428 364
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
              (364 364
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (364 364
                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
              (364 364 (:TYPE-PRESCRIPTION INTEGERP-MOD))
              (320 32 (:LINEAR MOD-BOUNDS-2))
              (320 32 (:LINEAR MOD-BOUNDS-1))
              (304 40
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (233 15 (:REWRITE MOD-ZERO . 3))
              (207 99 (:REWRITE DEFAULT-+-2))
              (180 40
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (170 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (161 161
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
              (157 157 (:REWRITE |(< (- x) (- y))|))
              (122 122 (:REWRITE DEFAULT-<-2))
              (122 122 (:REWRITE DEFAULT-<-1))
              (116 116
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (116 116 (:REWRITE DEFAULT-*-2))
              (116 116 (:REWRITE DEFAULT-*-1))
              (99 99
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (99 99 (:REWRITE DEFAULT-+-1))
              (97 97
                  (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
              (85 39 (:META META-INTEGERP-CORRECT))
              (63 63
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
              (63 63 (:REWRITE DEFAULT-UNARY-/))
              (60 60 (:REWRITE |(< 0 (- x))|))
              (60 60 (:REWRITE |(< (- x) 0)|))
              (60 60 (:REWRITE |(- (- x))|))
              (53 53 (:REWRITE DEFAULT-UNARY-MINUS))
              (48 48
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
              (48 48
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
              (40 40 (:REWRITE |(equal (- x) (- y))|))
              (39 39 (:REWRITE INTEGERP-MINUS-X))
              (28 28 (:REWRITE |(- (* c x))|))
              (25 25 (:REWRITE |(equal (- x) 0)|))
              (24 24 (:REWRITE MOD-COMPLETION))
              (22 22
                  (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
              (19 19 (:REWRITE |(< (+ c x) d)|))
              (17 17 (:REWRITE MOD-NEG))
              (17 17 (:REWRITE MOD-MINUS-2))
              (17 17 (:REWRITE MOD-CANCEL-*))
              (17 17 (:REWRITE |(< d (+ c x))|))
              (16 16 (:REWRITE |(integerp (* c x))|))
              (15 15
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
              (15 15 (:REWRITE MOD-X-Y-=-X . 2))
              (12 12 (:REWRITE |(equal (+ c x) d)|))
              (8 8 (:REWRITE FOLD-CONSTS-IN-+))
              (8 8 (:REWRITE ARITH-NORMALIZE-ADDENDS))
              (8 2 (:REWRITE |(* y (* x z))|))
              (4 4 (:REWRITE |(< (+ c x y) d)|))
              (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
              (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
              (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
              (3 3
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
              (2 2 (:REWRITE |(equal (+ c x y) d)|))
              (2 2 (:REWRITE |(< d (+ c x y))|))
              (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
              (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
              (2 2 (:REWRITE |(* c (* d x))|)))
(SIMPLIFY-MOD-+-MOD-FN
     (2420 855 (:REWRITE DEFAULT-+-2))
     (2238 168 (:DEFINITION LENGTH))
     (2183 118 (:DEFINITION INTEGER-ABS))
     (1848 238 (:DEFINITION LEN))
     (1625 1625 (:TYPE-PRESCRIPTION LEN))
     (1121 59 (:REWRITE |(+ (if a b c) x)|))
     (1049 855 (:REWRITE DEFAULT-+-1))
     (855 855
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (795 535 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (795 535
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (795 535
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (649 59 (:REWRITE NUMERATOR-NEGATIVE))
     (535 535 (:REWRITE |(equal (- x) (- y))|))
     (402 134
          (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (386 134 (:REWRITE DEFAULT-UNARY-MINUS))
     (285 221
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (256 154
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (256 154
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (247 247
          (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (242 242 (:REWRITE FOLD-CONSTS-IN-+))
     (236 236
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (236 236
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (236 236
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (236 236
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (222 222
          (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (221 221
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (213 213 (:REWRITE |(< (- x) (- y))|))
     (189 146 (:REWRITE DEFAULT-<-2))
     (177 177 (:REWRITE |(< (- x) 0)|))
     (166 146 (:REWRITE DEFAULT-<-1))
     (149 44 (:REWRITE |(< d (+ c x))|))
     (118 118
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (114 38 (:DEFINITION SYMBOL-LISTP))
     (111 111 (:REWRITE DEFAULT-COERCE-2))
     (111 111 (:REWRITE DEFAULT-COERCE-1))
     (64 32 (:REWRITE |(equal (+ c x) d)|))
     (59 59 (:REWRITE REDUCE-INTEGERP-+))
     (59 59 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (59 59
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (59 59 (:REWRITE INTEGERP-MINUS-X))
     (59 59 (:REWRITE DEFAULT-REALPART))
     (59 59 (:REWRITE DEFAULT-NUMERATOR))
     (59 59 (:REWRITE DEFAULT-IMAGPART))
     (59 59 (:REWRITE DEFAULT-DENOMINATOR))
     (59 59 (:META META-INTEGERP-CORRECT))
     (48 24 (:REWRITE |(< d (+ c x y))|))
     (47 8 (:REWRITE |(< (+ d x) (+ c y))|))
     (38 38 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (38 38
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (38 38 (:REWRITE |(equal (- x) 0)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (8 8 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (8 8 (:REWRITE |(< 0 (- x))|)))
(SIMPLIFY-MOD-+-MOD-WEAK
     (5810 64 (:LINEAR MOD-BOUNDS-3))
     (3794 157 (:META META-INTEGERP-CORRECT))
     (3696 1575 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2849 439
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2128 49 (:REWRITE MOD-ZERO . 2))
     (2052 1575 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (1837 157 (:REWRITE INTEGERP-MINUS-X))
     (1575 1575
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1575 1575
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1575 1575
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1575 1575
           (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (1575 1575
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1575 1575
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1517 49 (:REWRITE MOD-X-Y-=-X . 4))
     (1517 49 (:REWRITE MOD-X-Y-=-X . 3))
     (1406 49 (:REWRITE MOD-ZERO . 3))
     (1186 134
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1022 1022
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (917 131 (:REWRITE DEFAULT-+-2))
     (786 76 (:REWRITE DEFAULT-UNARY-MINUS))
     (764 26 (:REWRITE |(* (- x) y)|))
     (696 128 (:LINEAR MOD-BOUNDS-2))
     (696 128 (:LINEAR MOD-BOUNDS-1))
     (690 54 (:REWRITE |(- (- x))|))
     (671 241 (:REWRITE DEFAULT-*-2))
     (474 134
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (469 129 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (315 131 (:REWRITE DEFAULT-+-1))
     (241 241
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (241 241 (:REWRITE DEFAULT-*-1))
     (230 10 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (220 170 (:REWRITE DEFAULT-<-2))
     (220 170 (:REWRITE DEFAULT-<-1))
     (199 199
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (195 195 (:REWRITE |(< (- x) (- y))|))
     (177 159 (:REWRITE DEFAULT-UNARY-/))
     (159 159
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (148 98 (:REWRITE MOD-COMPLETION))
     (135 135
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (134 134 (:REWRITE |(equal (- x) (- y))|))
     (133 49 (:REWRITE MOD-X-Y-=-X . 2))
     (131 131
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (124 124 (:REWRITE |(equal (- x) 0)|))
     (119 119
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (110 110 (:REWRITE |(integerp (* c x))|))
     (99 49 (:REWRITE MOD-NEG))
     (99 49 (:REWRITE MOD-CANCEL-*))
     (84 84 (:REWRITE |(< 0 (- x))|))
     (84 84 (:REWRITE |(< (- x) 0)|))
     (77 77
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (77 77
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (49 49 (:REWRITE MOD-MINUS-2))
     (48 48 (:REWRITE |(- (* c x))|))
     (30 30 (:REWRITE FOLD-CONSTS-IN-+))
     (22 22
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (22 22 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (18 2 (:REWRITE |(* y (* x z))|))
     (17 17 (:REWRITE |(< (+ c x) d)|))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (15 15 (:REWRITE |(< d (+ c x))|))
     (10 10 (:REWRITE |(equal (+ c x) d)|))
     (10 10 (:REWRITE |(* c (* d x))|))
     (8 8 (:REWRITE |arith (+ c (+ d x))|))
     (7 7 (:REWRITE |(< (+ c x y) d)|))
     (5 5 (:REWRITE |(equal (+ c x y) d)|))
     (5 5 (:REWRITE |(< d (+ c x y))|))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
     (2 2 (:REWRITE |(< (+ c x) (+ d y))|)))
(SIMPLIFY-MOD-+-MINUS-MOD-FN
     (6419 2270 (:REWRITE DEFAULT-+-2))
     (4958 268 (:DEFINITION INTEGER-ABS))
     (2777 2270 (:REWRITE DEFAULT-+-1))
     (2546 134 (:REWRITE |(+ (if a b c) x)|))
     (2397 1632
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2391 1632 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2391 1632
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2270 2270
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1632 1632 (:REWRITE |(equal (- x) (- y))|))
     (1474 134 (:REWRITE NUMERATOR-NEGATIVE))
     (1074 358
           (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (994 994
          (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (876 304 (:REWRITE DEFAULT-UNARY-MINUS))
     (838 838
          (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (629 629 (:REWRITE FOLD-CONSTS-IN-+))
     (603 491
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (571 339
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (571 339
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (536 536
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (536 536
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (536 536
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (536 536
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (491 491
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (473 473 (:REWRITE |(< (- x) (- y))|))
     (471 157 (:DEFINITION SYMBOL-LISTP))
     (419 321 (:REWRITE DEFAULT-<-2))
     (402 402 (:REWRITE |(< (- x) 0)|))
     (356 321 (:REWRITE DEFAULT-<-1))
     (349 89 (:REWRITE |(< d (+ c x))|))
     (292 292 (:REWRITE DEFAULT-COERCE-2))
     (292 292 (:REWRITE DEFAULT-COERCE-1))
     (268 268
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (136 68 (:REWRITE |(equal (+ c x) d)|))
     (134 134 (:REWRITE REDUCE-INTEGERP-+))
     (134 134 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (134 134
          (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (134 134 (:REWRITE INTEGERP-MINUS-X))
     (134 134 (:REWRITE DEFAULT-REALPART))
     (134 134 (:REWRITE DEFAULT-NUMERATOR))
     (134 134 (:REWRITE DEFAULT-IMAGPART))
     (134 134 (:REWRITE DEFAULT-DENOMINATOR))
     (134 134 (:META META-INTEGERP-CORRECT))
     (117 18 (:REWRITE |(< (+ d x) (+ c y))|))
     (108 54 (:REWRITE |(< d (+ c x y))|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (22 22 (:REWRITE |(equal (- x) 0)|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (18 18 (:REWRITE |(< 0 (- x))|))
     (14 14 (:REWRITE ARITH-NORMALIZE-ADDENDS)))
(SIMPLIFY-MOD-+-MINUS-MOD
     (744 2 (:LINEAR MOD-BOUNDS-3))
     (387 151 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (354 14 (:META META-INTEGERP-CORRECT))
     (206 4 (:REWRITE |(* (+ x y) z)|))
     (187 151 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (157 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (151 151
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (151 151
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (151 151
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (151 151
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (151 151
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (151 151
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (144 12 (:REWRITE DEFAULT-+-2))
     (122 122
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (122 122
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (122 122
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (80 4 (:LINEAR MOD-BOUNDS-2))
     (80 4 (:LINEAR MOD-BOUNDS-1))
     (58 18 (:REWRITE DEFAULT-*-2))
     (58 6 (:REWRITE CANCEL-MOD-+))
     (54 14 (:REWRITE INTEGERP-MINUS-X))
     (46 6 (:REWRITE MOD-X-Y-=-X . 4))
     (46 6 (:REWRITE MOD-X-Y-=-X . 3))
     (45 6 (:REWRITE MOD-ZERO . 2))
     (36 12 (:REWRITE DEFAULT-+-1))
     (32 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (30 6 (:REWRITE MOD-ZERO . 3))
     (20 2 (:REWRITE |(* (- x) y)|))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 18 (:REWRITE DEFAULT-*-1))
     (18 6 (:REWRITE MOD-X-Y-=-X . 2))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 16 (:REWRITE SIMPLIFY-SUMS-<))
     (16 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (16 16
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (16 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (16 16 (:REWRITE DEFAULT-<-2))
     (16 16 (:REWRITE DEFAULT-<-1))
     (16 16 (:REWRITE |(equal (- x) 0)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (16 16 (:REWRITE |(< (- x) (- y))|))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (14 14 (:REWRITE DEFAULT-UNARY-/))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE MOD-COMPLETION))
     (11 11 (:REWRITE |(+ c (+ d x))|))
     (10 10 (:REWRITE |(integerp (* c x))|))
     (10 2 (:REWRITE |(- (- x))|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (8 8
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (8 8 (:REWRITE |(< 0 (- x))|))
     (8 8 (:REWRITE |(< (- x) 0)|))
     (6 6 (:REWRITE MOD-NEG))
     (6 6 (:REWRITE MOD-MINUS-2))
     (6 6 (:REWRITE MOD-CANCEL-*))
     (4 4 (:REWRITE |(- (* c x))|))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT)))
(FLOOR-0-LOCAL-2 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)))
(FLOOR-FLOOR-INTEGER-ALT
     (4427 4427
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4108 46 (:LINEAR FLOOR-BOUNDS-3))
     (4108 46 (:LINEAR FLOOR-BOUNDS-2))
     (3643 91 (:REWRITE FLOOR-ZERO . 4))
     (3032 404 (:REWRITE DEFAULT-+-2))
     (2137 517 (:REWRITE DEFAULT-UNARY-/))
     (1915 1011 (:REWRITE DEFAULT-*-2))
     (1728 1728
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1728 1728
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1728 1728
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1728 1728
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1728 1728
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1691 1691
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (1662 398
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (1460 308
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (1460 308
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (1460 308
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (1203 368 (:META META-INTEGERP-CORRECT))
     (1011 1011
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1011 1011 (:REWRITE DEFAULT-*-1))
     (926 926
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (926 926
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (926 926
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (872 872 (:REWRITE |arith (* c (* d x))|))
     (700 510
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (700 510
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (626 90 (:REWRITE FLOOR-ZERO . 2))
     (596 596 (:REWRITE |(* c (* d x))|))
     (517 517
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (516 404 (:REWRITE DEFAULT-+-1))
     (510 510 (:REWRITE |(equal (- x) (- y))|))
     (502 502
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (502 502 (:REWRITE |(equal (- x) 0)|))
     (472 328 (:REWRITE DEFAULT-<-2))
     (472 328 (:REWRITE DEFAULT-<-1))
     (415 415
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (404 404
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (398 398
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (398 398
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (398 398
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (389 389 (:REWRITE |(< (- x) (- y))|))
     (368 368 (:REWRITE INTEGERP-MINUS-X))
     (308 308
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4F))
     (308 308
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3F))
     (308 308
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2F))
     (308 308
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1F))
     (235 91 (:REWRITE FLOOR-MINUS-WEAK))
     (235 91 (:REWRITE FLOOR-MINUS-2))
     (234 90 (:REWRITE FLOOR-COMPLETION))
     (232 232 (:REWRITE |arith (* (- x) y)|))
     (220 220 (:REWRITE |arith (- (* c x))|))
     (147 147 (:REWRITE |(integerp (* c x))|))
     (147 147 (:REWRITE |(< (- x) 0)|))
     (133 133
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (115 115 (:REWRITE |(< 0 (- x))|))
     (107 107
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (72 72 (:REWRITE FOLD-CONSTS-IN-+))
     (71 71 (:REWRITE DEFAULT-UNARY-MINUS))
     (36 36 (:REWRITE |(- (* c x))|))
     (34 34 (:REWRITE |(< d (+ c x))|))
     (20 20 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (16 16 (:REWRITE |(< (+ d x) (+ c y))|))
     (16 16 (:REWRITE |(< (+ c x) (+ d y))|))
     (12 12 (:REWRITE FLOOR-POSITIVE . 3))
     (12 12 (:REWRITE FLOOR-POSITIVE . 2))
     (12 12 (:REWRITE FLOOR-POSITIVE . 1))
     (12 12 (:REWRITE FLOOR-NONPOSITIVE-2))
     (12 12 (:REWRITE FLOOR-NONPOSITIVE-1))
     (12 12 (:REWRITE FLOOR-NONNEGATIVE-2))
     (12 12 (:REWRITE FLOOR-NONNEGATIVE-1))
     (12 12 (:REWRITE FLOOR-NEGATIVE . 3))
     (12 12 (:REWRITE FLOOR-NEGATIVE . 2))
     (12 12 (:REWRITE FLOOR-NEGATIVE . 1))
     (10 10 (:REWRITE |(equal (+ c x) d)|))
     (10 10 (:REWRITE |(< (+ c x y) d)|))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (5 5 (:REWRITE |(< d (+ c x y))|))
     (4 4
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT)))
(MOD-TWO (399 83 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
         (399 83
              (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
         (208 208
              (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
         (208 208
              (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
         (208 208
              (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
         (208 208
              (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
         (88 8 (:REWRITE MOD-X-Y-=-X . 4))
         (88 8 (:REWRITE MOD-X-Y-=-X . 3))
         (84 8 (:REWRITE MOD-ZERO . 2))
         (83 83 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
         (83 83
             (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
         (83 83 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
         (83 83
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
         (83 83
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
         (52 8 (:REWRITE CANCEL-MOD-+))
         (27 3 (:LINEAR MOD-BOUNDS-3))
         (21 21
             (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
         (21 21 (:REWRITE DEFAULT-*-2))
         (21 21 (:REWRITE DEFAULT-*-1))
         (21 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (21 3
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (21 3
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
         (16 16 (:REWRITE SIMPLIFY-SUMS-<))
         (16 16
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
         (16 16
             (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
         (16 16
             (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
         (16 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
         (16 16 (:REWRITE MOD-COMPLETION))
         (16 16 (:REWRITE DEFAULT-<-2))
         (16 16 (:REWRITE DEFAULT-<-1))
         (16 16 (:REWRITE |(< (- x) (- y))|))
         (14 8 (:REWRITE MOD-ZERO . 3))
         (8 8
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
         (8 8
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
         (8 8 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
         (8 8 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
         (8 8 (:REWRITE MOD-X-Y-=-X . 2))
         (8 8 (:REWRITE MOD-NEG))
         (8 8 (:REWRITE MOD-MINUS-2))
         (8 8 (:REWRITE MOD-CANCEL-*))
         (8 8 (:REWRITE |(< 0 (- x))|))
         (8 8 (:REWRITE |(< (- x) 0)|))
         (6 6 (:LINEAR MOD-BOUNDS-2))
         (4 4 (:REWRITE REDUCE-INTEGERP-+))
         (4 4 (:REWRITE INTEGERP-MINUS-X))
         (4 4 (:META META-INTEGERP-CORRECT))
         (3 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
         (3 3 (:REWRITE |(integerp (* c x))|))
         (3 3 (:REWRITE |(equal (- x) (- y))|))
         (2 2
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
         (2 2 (:REWRITE |(equal (- x) 0)|)))
(FLOOR-0 (2 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
         (2 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
         (2 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
         (2 2
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)))
(MOD-0 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
       (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
       (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
       (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
       (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
       (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
       (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
       (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
       (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD)))
(FLOOR-X-1 (66 4 (:LINEAR FLOOR-BOUNDS-1))
           (28 2 (:LINEAR FLOOR-BOUNDS-2))
           (25 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
           (25 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
           (25 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
           (25 25
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
           (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
           (2 2
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (2 2 (:REWRITE DEFAULT-+-2))
           (2 2 (:REWRITE DEFAULT-+-1))
           (2 2 (:LINEAR FLOOR-BOUNDS-3))
           (1 1 (:REWRITE REDUCE-INTEGERP-+))
           (1 1 (:REWRITE INTEGERP-MINUS-X))
           (1 1 (:META META-INTEGERP-CORRECT)))
(MOD-X-1 (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
         (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
         (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
         (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
         (1 1
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)))
