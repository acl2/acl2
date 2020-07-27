(INTEGERP-OF-MOD (7 3 (:REWRITE DEFAULT-*-1))
                 (7 1
                    (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                 (6 6
                    (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                 (6 6
                    (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                 (6 6
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (6 3 (:REWRITE DEFAULT-*-2))
                 (6 1
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                 (4 1 (:REWRITE FLOOR-WHEN-<))
                 (4 1 (:REWRITE DEFAULT-UNARY-MINUS))
                 (4 1 (:REWRITE DEFAULT-+-2))
                 (2 1
                    (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                 (2 1 (:REWRITE DEFAULT-<-1))
                 (2 1 (:REWRITE DEFAULT-+-1))
                 (1 1 (:REWRITE RATIONALP-*))
                 (1 1
                    (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
                 (1 1
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                 (1 1
                    (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                 (1 1
                    (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                 (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                 (1 1 (:REWRITE DEFAULT-UNARY-/))
                 (1 1 (:REWRITE DEFAULT-<-2)))
(INTEGERP-OF-MOD-TYPE (7 1
                         (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                      (5 5
                         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                      (5 5
                         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                      (5 2 (:REWRITE DEFAULT-*-2))
                      (5 2 (:REWRITE DEFAULT-*-1))
                      (4 1 (:REWRITE DEFAULT-UNARY-MINUS))
                      (4 1 (:REWRITE DEFAULT-+-2))
                      (3 1 (:REWRITE FLOOR-WHEN-<))
                      (1 1
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                      (1 1
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                      (1 1
                         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                      (1 1
                         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                      (1 1
                         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                      (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                      (1 1 (:REWRITE DEFAULT-<-2))
                      (1 1 (:REWRITE DEFAULT-<-1))
                      (1 1 (:REWRITE DEFAULT-+-1)))
(NONNEG-OF-MOD-TYPE (67 67
                        (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                    (61 61
                        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                    (61 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                    (57 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                    (47 3
                        (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                    (38 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
                    (19 13 (:REWRITE DEFAULT-<-2))
                    (18 9 (:REWRITE DEFAULT-*-2))
                    (16 13 (:REWRITE DEFAULT-<-1))
                    (15 9 (:REWRITE DEFAULT-*-1))
                    (14 6 (:REWRITE FLOOR-WHEN-<))
                    (10 4 (:REWRITE DEFAULT-+-2))
                    (8 2 (:REWRITE DEFAULT-UNARY-MINUS))
                    (6 6
                       (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                    (6 6
                       (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                    (6 6
                       (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                    (6 6
                       (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                    (6 6
                       (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                    (6 6 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                    (6 6
                       (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                    (6 6 (:LINEAR <-OF-*-AND-*))
                    (4 4 (:REWRITE DEFAULT-+-1))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                    (3 1
                       (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
                    (2 2 (:REWRITE DEFAULT-UNARY-/))
                    (2 2 (:REWRITE *-OF-0))
                    (2 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                    (1 1 (:TYPE-PRESCRIPTION NATP))
                    (1 1 (:REWRITE <-OF-0-AND-FLOOR))
                    (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                    (1 1
                       (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                    (1 1 (:DEFINITION NATP)))
(NONNEG-OF-MOD-TYPE-2 (55 3
                          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                      (39 39
                          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                      (39 39
                          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                      (17 17
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                      (17 17
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                      (14 5 (:REWRITE DEFAULT-*-2))
                      (11 5 (:REWRITE DEFAULT-*-1))
                      (8 5 (:REWRITE DEFAULT-<-1))
                      (8 2 (:REWRITE DEFAULT-UNARY-MINUS))
                      (8 2 (:REWRITE DEFAULT-+-2))
                      (7 3 (:REWRITE FLOOR-WHEN-<))
                      (5 5 (:REWRITE DEFAULT-<-2))
                      (5 1
                         (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
                      (3 3
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                      (3 3
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                      (3 3
                         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                      (3 3
                         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                      (3 3
                         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                      (3 3 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                      (3 1 (:DEFINITION NATP))
                      (2 2 (:REWRITE DEFAULT-+-1))
                      (1 1 (:TYPE-PRESCRIPTION NATP))
                      (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                      (1 1
                         (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(MOD-OF-0-ARG1 (9 9
                  (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
               (9 9
                  (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
               (9 9
                  (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
               (4 1 (:REWRITE FLOOR-WHEN-<))
               (2 1 (:REWRITE DEFAULT-<-2))
               (1 1
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (1 1
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
               (1 1
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
               (1 1
                  (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
               (1 1
                  (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
               (1 1
                  (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
               (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
               (1 1 (:REWRITE DEFAULT-<-1)))
(MOD-OF-0-ARG2 (15 15
                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
               (15 15
                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
               (15 15
                   (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
               (6 6
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (4 1 (:REWRITE FLOOR-WHEN-<))
               (3 2 (:REWRITE DEFAULT-+-2))
               (3 2 (:REWRITE DEFAULT-+-1))
               (2 1
                  (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
               (2 1 (:REWRITE DEFAULT-<-1))
               (1 1
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
               (1 1
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
               (1 1
                  (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
               (1 1
                  (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
               (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
               (1 1 (:REWRITE DEFAULT-<-2)))
(MOD-OF-1-WHEN-INTEGERP (3 1 (:REWRITE FLOOR-WHEN-<))
                        (2 2
                           (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                        (2 2 (:REWRITE DEFAULT-*-2))
                        (2 2 (:REWRITE DEFAULT-*-1))
                        (1 1
                           (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                        (1 1
                           (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                        (1 1
                           (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                        (1 1
                           (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                        (1 1
                           (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                        (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                        (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                        (1 1 (:REWRITE DEFAULT-<-2))
                        (1 1 (:REWRITE DEFAULT-<-1))
                        (1 1 (:REWRITE DEFAULT-+-2))
                        (1 1 (:REWRITE DEFAULT-+-1)))
(MOD-OF-1-ARG1 (27 27
                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
               (3 1 (:REWRITE FLOOR-WHEN-<))
               (2 2 (:REWRITE DEFAULT-<-2))
               (2 2 (:REWRITE DEFAULT-<-1))
               (2 2 (:REWRITE DEFAULT-*-2))
               (2 2 (:REWRITE DEFAULT-*-1))
               (1 1
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
               (1 1
                  (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
               (1 1
                  (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
               (1 1
                  (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
               (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
               (1 1
                  (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
               (1 1
                  (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
               (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
               (1 1 (:REWRITE DEFAULT-+-2))
               (1 1 (:REWRITE DEFAULT-+-1)))
(RATIONALP-OF-MOD (64 64
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                  (64 64
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                  (64 64
                      (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                  (25 1
                      (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                  (10 3 (:REWRITE FLOOR-WHEN-<))
                  (8 5 (:REWRITE DEFAULT-+-2))
                  (7 3
                     (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                  (6 3 (:REWRITE DEFAULT-*-1))
                  (5 5
                     (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                  (5 5
                     (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                  (5 5 (:REWRITE DEFAULT-+-1))
                  (5 4 (:REWRITE DEFAULT-<-2))
                  (4 1 (:REWRITE DEFAULT-UNARY-MINUS))
                  (3 3
                     (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                  (3 3
                     (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                  (3 3
                     (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                  (3 3 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                  (3 3 (:REWRITE DEFAULT-<-1))
                  (2 2
                     (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                  (1 1 (:REWRITE RATIONALP-*))
                  (1 1 (:REWRITE DEFAULT-UNARY-/)))
(MOD-OF-MOD-SAME-ARG2
     (695 307 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (367 307
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (367 307 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (299 299
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (299 299
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (299 299
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (299 299
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (293 293
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (293 293
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (226 10 (:REWRITE MOD-X-Y-=-X . 4))
     (226 10 (:REWRITE MOD-X-Y-=-X . 3))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (180 10 (:REWRITE MOD-ZERO . 3))
     (150 12 (:LINEAR MOD-BOUNDS-3))
     (131 10 (:REWRITE CANCEL-MOD-+))
     (126 10 (:REWRITE MOD-ZERO . 2))
     (108 48 (:REWRITE SIMPLIFY-SUMS-<))
     (108 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (87 23
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (78 48 (:REWRITE DEFAULT-<-2))
     (78 48 (:REWRITE DEFAULT-<-1))
     (74 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (74 23
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (50 50
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (50 50 (:REWRITE |(< (- x) (- y))|))
     (49 16 (:REWRITE INTEGERP-OF-*))
     (36 36
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (33 20 (:REWRITE MOD-COMPLETION))
     (31 5 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (28 28 (:REWRITE REDUCE-INTEGERP-+))
     (28 28 (:REWRITE INTEGERP-MINUS-X))
     (28 28 (:META META-INTEGERP-CORRECT))
     (27 27
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (27 27 (:REWRITE DEFAULT-UNARY-/))
     (26 26
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (24 24 (:REWRITE |(< 0 (- x))|))
     (23 23 (:REWRITE |(equal (- x) (- y))|))
     (23 10 (:REWRITE MOD-NEG))
     (23 10 (:REWRITE MOD-CANCEL-*))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (22 22 (:REWRITE |(< (- x) 0)|))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 20 (:REWRITE DEFAULT-*-2))
     (20 20 (:REWRITE DEFAULT-*-1))
     (20 20 (:REWRITE |(equal (- x) 0)|))
     (16 16 (:REWRITE |(integerp (* c x))|))
     (16 10 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (16 10 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (10 10 (:REWRITE MOD-X-Y-=-X . 2))
     (10 10 (:REWRITE MOD-MINUS-2))
     (7 1 (:REWRITE REWRITE-MOD-MOD-WEAK))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
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
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE MOD-POSITIVE . 3))
     (2 2 (:REWRITE MOD-POSITIVE . 2))
     (2 2 (:REWRITE MOD-NEGATIVE . 3))
     (2 2 (:REWRITE MOD-NEGATIVE . 2))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-NONPOSITIVE))
     (1 1 (:REWRITE MOD-NONNEGATIVE)))
(MOD-WHEN-< (140 5 (:REWRITE CANCEL-MOD-+))
            (64 2 (:LINEAR MOD-BOUNDS-3))
            (55 5 (:REWRITE MOD-X-Y-=-X . 4))
            (49 7 (:REWRITE DEFAULT-UNARY-/))
            (40 4 (:LINEAR MOD-BOUNDS-2))
            (31 31
                (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
            (31 31
                (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
            (31 31 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
            (31 31 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
            (31 31
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
            (31 31
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
            (31 31 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
            (31 31 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
            (31 31
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
            (31 31
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
            (31 31
                (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
            (31 31 (:TYPE-PRESCRIPTION INTEGERP-MOD))
            (28 7 (:REWRITE INTEGERP-OF-*))
            (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (14 14 (:REWRITE REDUCE-INTEGERP-+))
            (14 14 (:REWRITE INTEGERP-MINUS-X))
            (14 14 (:META META-INTEGERP-CORRECT))
            (11 11 (:REWRITE SIMPLIFY-SUMS-<))
            (11 11
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (11 11
                (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
            (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
            (11 11 (:REWRITE DEFAULT-<-2))
            (11 11 (:REWRITE DEFAULT-<-1))
            (11 11 (:REWRITE |(< (- x) (- y))|))
            (7 7
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
            (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (7 7
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (7 7
               (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
            (7 7
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (7 7
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (7 7
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (7 7 (:REWRITE DEFAULT-*-2))
            (7 7 (:REWRITE DEFAULT-*-1))
            (7 7 (:REWRITE |(integerp (* c x))|))
            (7 7 (:REWRITE |(equal (- x) 0)|))
            (7 7 (:REWRITE |(equal (- x) (- y))|))
            (5 5
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
            (5 5
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
            (5 5 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
            (5 5 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
            (5 5 (:REWRITE MOD-NEG))
            (5 5 (:REWRITE MOD-MINUS-2))
            (5 5 (:REWRITE MOD-CANCEL-*))
            (5 5 (:REWRITE |(< 0 (- x))|))
            (5 5 (:REWRITE |(< (- x) 0)|))
            (2 2
               (:TYPE-PRESCRIPTION RATIONALP-OF-MOD)))
(EQUAL-OF-0-AND-MOD (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                    (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (22 22
                        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                    (22 22
                        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                    (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                    (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                    (22 22
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                    (22 22
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                    (22 22 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                    (22 22 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                    (22 22
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                    (22 22
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                    (22 22
                        (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                    (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                    (11 1 (:REWRITE MOD-X-Y-=-X . 4))
                    (11 1 (:REWRITE MOD-X-Y-=-X . 3))
                    (9 9
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                    (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (9 9
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (9 9
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (9 9 (:REWRITE |(equal (- x) 0)|))
                    (9 9 (:REWRITE |(equal (- x) (- y))|))
                    (8 2 (:REWRITE INTEGERP-OF-*))
                    (8 1 (:REWRITE MOD-WHEN-<))
                    (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                    (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                    (7 1 (:REWRITE MOD-ZERO . 3))
                    (7 1 (:REWRITE MOD-ZERO . 2))
                    (7 1 (:REWRITE CANCEL-MOD-+))
                    (4 4 (:REWRITE REDUCE-INTEGERP-+))
                    (4 4 (:REWRITE INTEGERP-MINUS-X))
                    (4 4 (:META META-INTEGERP-CORRECT))
                    (3 3 (:REWRITE SIMPLIFY-SUMS-<))
                    (3 3
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                    (3 3
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                    (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                    (3 3 (:REWRITE DEFAULT-<-2))
                    (3 3 (:REWRITE DEFAULT-<-1))
                    (3 3 (:REWRITE |(< (- x) (- y))|))
                    (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                    (2 2
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                    (2 2
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                    (2 2
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (2 2 (:REWRITE MOD-COMPLETION))
                    (2 2 (:REWRITE DEFAULT-UNARY-/))
                    (2 2 (:REWRITE DEFAULT-*-2))
                    (2 2 (:REWRITE DEFAULT-*-1))
                    (2 2 (:REWRITE |(integerp (* c x))|))
                    (1 1
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                    (1 1
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                    (1 1 (:REWRITE MOD-X-Y-=-X . 2))
                    (1 1 (:REWRITE MOD-NEG))
                    (1 1 (:REWRITE MOD-MINUS-2))
                    (1 1 (:REWRITE MOD-CANCEL-*))
                    (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
                    (1 1 (:REWRITE |(< 0 (- x))|))
                    (1 1 (:REWRITE |(< (- x) 0)|)))
(INTEGERP-OF-*-OF-/-BECOMES-EQUAL-OF-0-AND-MOD
     (121 33 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (46 2 (:REWRITE MOD-ZERO . 2))
     (44 2 (:REWRITE CANCEL-MOD-+))
     (33 33
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (33 33
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (33 33 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (33 33
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (33 33
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (33 33 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (33 33 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (33 33
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (33 33
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (33 33
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (33 33 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (23 8 (:REWRITE INTEGERP-OF-*))
     (22 2 (:REWRITE MOD-X-Y-=-X . 4))
     (22 2 (:REWRITE MOD-X-Y-=-X . 3))
     (16 2 (:REWRITE MOD-WHEN-<))
     (14 2 (:REWRITE MOD-ZERO . 3))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 8 (:REWRITE DEFAULT-UNARY-/))
     (8 8 (:REWRITE DEFAULT-*-2))
     (8 8 (:REWRITE DEFAULT-*-1))
     (8 8 (:REWRITE |(integerp (* c x))|))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:REWRITE |(equal (- x) 0)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (4 4
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (4 4 (:REWRITE MOD-COMPLETION))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (2 2 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (2 2 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (2 2 (:REWRITE MOD-X-Y-=-X . 2))
     (2 2 (:REWRITE MOD-NEG))
     (2 2 (:REWRITE MOD-MINUS-2))
     (2 2 (:REWRITE MOD-CANCEL-*))
     (2 2 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (2 2 (:REWRITE |(< 0 (- x))|))
     (2 2 (:REWRITE |(< (- x) 0)|)))
(MOD-BOUND-LINEAR-ARG1
     (597 10 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (576 5 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (434 4 (:LINEAR FLOOR-BOUNDS-1))
     (261 89 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (245 89
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (242 11 (:REWRITE CANCEL-FLOOR-+))
     (192 5
          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (174 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (169 169
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (169 169
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (169 169
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (169 169
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (121 11 (:REWRITE FLOOR-ZERO . 4))
     (108 43 (:REWRITE DEFAULT-*-2))
     (94 8 (:REWRITE DEFAULT-+-2))
     (89 89 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (89 89
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (89 89 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (89 89
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (89 89
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (89 89
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (89 89 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (88 11 (:REWRITE FLOOR-ZERO . 3))
     (88 11 (:REWRITE FLOOR-WHEN-<))
     (84 58 (:REWRITE DEFAULT-<-2))
     (79 22 (:REWRITE INTEGERP-OF-*))
     (70 4 (:REWRITE MOD-ZERO . 2))
     (66 3 (:REWRITE CANCEL-MOD-+))
     (64 64
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (61 61 (:REWRITE |(< (- x) (- y))|))
     (58 58 (:REWRITE DEFAULT-<-1))
     (56 56 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (56 56 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (56 56 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (56 56
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (55 11
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (52 2 (:LINEAR FLOOR-BOUNDS-3))
     (52 2 (:LINEAR FLOOR-BOUNDS-2))
     (50 50
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (48 2
         (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
     (46 46 (:REWRITE REDUCE-INTEGERP-+))
     (46 46 (:REWRITE INTEGERP-MINUS-X))
     (46 46 (:META META-INTEGERP-CORRECT))
     (44 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (43 43
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (43 43 (:REWRITE DEFAULT-*-1))
     (43 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (35 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (34 4 (:REWRITE MOD-X-Y-=-X . 4))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (30 30 (:REWRITE DEFAULT-UNARY-/))
     (27 2 (:LINEAR MOD-BOUNDS-3))
     (26 5 (:REWRITE MOD-WHEN-<))
     (25 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (25 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (25 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (25 4 (:REWRITE MOD-X-Y-=-X . 3))
     (22 22 (:REWRITE |(integerp (* c x))|))
     (22 4 (:REWRITE MOD-ZERO . 3))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (19 19 (:REWRITE |(< 0 (- x))|))
     (11 11 (:REWRITE FLOOR-ZERO . 2))
     (11 11
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (11 11
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (11 11
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (11 11 (:REWRITE FLOOR-MINUS-WEAK))
     (11 11
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (11 11 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (11 11 (:REWRITE FLOOR-MINUS-2))
     (11 11 (:REWRITE FLOOR-COMPLETION))
     (11 11 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (10 10
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (10 10
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (10 10 (:LINEAR <-OF-*-AND-*))
     (9 1 (:REWRITE FLOOR-POSITIVE . 2))
     (9 1
        (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE MOD-COMPLETION))
     (8 8 (:REWRITE DEFAULT-+-1))
     (8 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (7 1 (:DEFINITION NATP))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (6 6 (:REWRITE |(equal (- x) 0)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (5 5 (:REWRITE |(< (- x) 0)|))
     (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (4 4 (:REWRITE MOD-X-Y-=-X . 2))
     (4 4 (:LINEAR MOD-BOUNDS-2))
     (4 1 (:REWRITE <-OF-0-AND-FLOOR))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (3 3 (:REWRITE MOD-NEG))
     (3 3 (:REWRITE MOD-MINUS-2))
     (3 3 (:REWRITE MOD-CANCEL-*))
     (3 3 (:REWRITE |(- (* c x))|))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:REWRITE |(* 0 x)|))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 1))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 2))
     (1 1 (:REWRITE |(< d (+ c x))|))
     (1 1 (:REWRITE |(< (+ c x) d)|)))
(<-OF-MOD-SAME-ARG2 (142 50 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                    (98 50
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                    (90 50
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                    (67 67 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                    (67 67 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (67 67 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (67 67 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (53 3 (:REWRITE MOD-ZERO . 2))
                    (52 2 (:LINEAR MOD-BOUNDS-3))
                    (51 3 (:REWRITE CANCEL-MOD-+))
                    (50 50 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                    (50 50
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                    (50 50
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                    (50 50
                        (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                    (50 50 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                    (50 18
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                    (50 18 (:REWRITE DEFAULT-<-1))
                    (38 38
                        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                    (38 38
                        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                    (33 3 (:REWRITE MOD-X-Y-=-X . 4))
                    (33 3 (:REWRITE MOD-X-Y-=-X . 3))
                    (31 18 (:REWRITE SIMPLIFY-SUMS-<))
                    (31 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                    (24 3 (:REWRITE MOD-WHEN-<))
                    (22 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                    (21 3 (:REWRITE MOD-ZERO . 3))
                    (18 18
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                    (18 18 (:REWRITE DEFAULT-<-2))
                    (18 18 (:REWRITE |(< (- x) (- y))|))
                    (18 6 (:REWRITE INTEGERP-OF-*))
                    (15 15
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                    (10 10
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                    (10 10 (:REWRITE REDUCE-INTEGERP-+))
                    (10 10 (:REWRITE INTEGERP-MINUS-X))
                    (10 10 (:REWRITE |(< (- x) 0)|))
                    (10 10 (:META META-INTEGERP-CORRECT))
                    (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (9 9
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (9 9
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (9 9 (:REWRITE |(equal (- x) (- y))|))
                    (9 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                    (9 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                    (8 8
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                    (8 8 (:REWRITE |(equal (- x) 0)|))
                    (6 6
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                    (6 6
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (6 6 (:REWRITE MOD-COMPLETION))
                    (6 6 (:REWRITE DEFAULT-UNARY-/))
                    (6 6 (:REWRITE DEFAULT-*-2))
                    (6 6 (:REWRITE DEFAULT-*-1))
                    (6 6 (:REWRITE |(integerp (* c x))|))
                    (3 3
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                    (3 3 (:REWRITE MOD-X-Y-=-X . 2))
                    (3 3 (:REWRITE MOD-NEG))
                    (3 3 (:REWRITE MOD-MINUS-2))
                    (3 3 (:REWRITE MOD-CANCEL-*))
                    (3 3 (:REWRITE |(< 0 (- x))|))
                    (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                    (1 1 (:REWRITE MOD-NEGATIVE . 3))
                    (1 1 (:REWRITE MOD-NEGATIVE . 2)))
(MOD-BOUND-LINEAR-ARG2
     (669 6 (:LINEAR FLOOR-BOUNDS-1))
     (537 8 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (534 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (531 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (308 14 (:REWRITE CANCEL-FLOOR-+))
     (273 3 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (199 51 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (199 51
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (192 5
          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (154 14 (:REWRITE FLOOR-ZERO . 4))
     (154 14 (:REWRITE FLOOR-ZERO . 3))
     (137 67
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (122 66 (:REWRITE SIMPLIFY-SUMS-<))
     (112 14 (:REWRITE FLOOR-WHEN-<))
     (111 41 (:REWRITE DEFAULT-*-2))
     (107 65 (:REWRITE DEFAULT-<-2))
     (99 27 (:REWRITE INTEGERP-OF-*))
     (90 8 (:REWRITE DEFAULT-+-2))
     (78 3 (:LINEAR FLOOR-BOUNDS-3))
     (78 3 (:LINEAR FLOOR-BOUNDS-2))
     (70 14
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (70 4 (:REWRITE MOD-ZERO . 2))
     (67 67
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (67 67 (:REWRITE |(< (- x) (- y))|))
     (66 3 (:REWRITE CANCEL-MOD-+))
     (65 65 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (65 65 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (65 65 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (65 65
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (65 65 (:REWRITE DEFAULT-<-1))
     (54 54 (:REWRITE REDUCE-INTEGERP-+))
     (54 54 (:REWRITE INTEGERP-MINUS-X))
     (54 54 (:META META-INTEGERP-CORRECT))
     (51 51 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (51 51
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (51 51 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (51 51
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (51 51
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (51 51
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (51 51 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (45 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (44 44
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (41 41
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (41 41 (:REWRITE DEFAULT-*-1))
     (36 36
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (36 36 (:REWRITE DEFAULT-UNARY-/))
     (34 4 (:REWRITE MOD-X-Y-=-X . 4))
     (34 4 (:REWRITE MOD-X-Y-=-X . 3))
     (33 3 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (27 27 (:REWRITE |(integerp (* c x))|))
     (26 1 (:LINEAR MOD-BOUNDS-3))
     (25 4 (:REWRITE MOD-WHEN-<))
     (23 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (23 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (23 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (22 22 (:REWRITE |(< (- x) 0)|))
     (22 4 (:REWRITE MOD-ZERO . 3))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (20 20 (:REWRITE |(< 0 (- x))|))
     (18 2 (:REWRITE FLOOR-POSITIVE . 2))
     (16 1
         (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (14 14
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (14 14
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (14 14 (:REWRITE FLOOR-ZERO . 2))
     (14 14
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (14 14
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (14 14
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (14 14 (:REWRITE FLOOR-MINUS-WEAK))
     (14 14
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (14 14 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (14 14 (:REWRITE FLOOR-MINUS-2))
     (14 14 (:REWRITE FLOOR-COMPLETION))
     (14 14 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (14 1 (:DEFINITION NATP))
     (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE MOD-COMPLETION))
     (8 8 (:REWRITE DEFAULT-+-1))
     (8 8
        (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (8 8 (:LINEAR <-OF-*-AND-*))
     (8 2 (:REWRITE <-OF-0-AND-FLOOR))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (4 4 (:REWRITE MOD-X-Y-=-X . 2))
     (4 4 (:REWRITE |(equal (- x) 0)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (3 3 (:REWRITE MOD-NEG))
     (3 3 (:REWRITE MOD-MINUS-2))
     (3 3 (:REWRITE MOD-CANCEL-*))
     (3 3 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE FLOOR-POSITIVE . 3))
     (2 2 (:REWRITE FLOOR-POSITIVE . 1))
     (2 2 (:LINEAR MOD-BOUNDS-2))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1 (:REWRITE |(< d (+ c x))|))
     (1 1 (:REWRITE |(< (+ c x) d)|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(EQUAL-OF-MOD-SAME-ARG1
     (96 24 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (96 24
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (24 24
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (24 24 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (24 24
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (24 24
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (24 24
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (23 1 (:REWRITE MOD-ZERO . 2))
     (22 1 (:REWRITE CANCEL-MOD-+))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 12
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE |(< (- x) (- y))|))
     (11 11
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (11 1 (:REWRITE MOD-X-Y-=-X . 4))
     (11 1 (:REWRITE MOD-X-Y-=-X . 3))
     (8 1 (:REWRITE MOD-WHEN-<))
     (7 1 (:REWRITE MOD-ZERO . 3))
     (6 6
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (6 6
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (5 2 (:REWRITE INTEGERP-OF-*))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (4 4 (:REWRITE |(< (- x) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< 0 (- x))|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE DEFAULT-UNARY-/))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 2 (:REWRITE |(integerp (* c x))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1 (:REWRITE |(equal (- x) 0)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(MOD-OF-2-WHEN-EVEN-CHEAP (80 16 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                          (80 16
                              (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                          (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                          (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                          (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                          (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                          (24 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
                          (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                          (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                          (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                          (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                          (16 16 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                          (16 16
                              (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                          (16 16 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                          (16 16
                              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                          (16 16
                              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                          (16 2 (:REWRITE MOD-WHEN-<))
                          (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                          (10 10
                              (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                          (5 5
                             (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                          (5 5 (:REWRITE DEFAULT-*-2))
                          (5 5 (:REWRITE DEFAULT-*-1))
                          (3 3 (:REWRITE SIMPLIFY-SUMS-<))
                          (3 3
                             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                          (3 3
                             (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                          (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                          (3 3 (:REWRITE DEFAULT-<-2))
                          (3 3 (:REWRITE DEFAULT-<-1))
                          (3 3 (:REWRITE |(< (- x) (- y))|))
                          (2 2 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                          (2 2 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                          (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                          (1 1
                             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                          (1 1
                             (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                          (1 1 (:REWRITE |(< (- x) 0)|)))
(MOD-OF-*-LEMMA (85 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
                (78 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                (71 17
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (65 13
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (41 1 (:REWRITE <-OF-*-AND-0))
                (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (30 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                (24 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                (17 17
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (17 17 (:REWRITE |(< (- x) (- y))|))
                (15 15 (:REWRITE SIMPLIFY-SUMS-<))
                (15 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (14 14 (:REWRITE DEFAULT-<-2))
                (14 14 (:REWRITE DEFAULT-<-1))
                (13 13
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (13 13 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (13 13
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (13 13
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (10 2 (:REWRITE |(* y (* x z))|))
                (9 9
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (9 9 (:REWRITE DEFAULT-UNARY-/))
                (7 7
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (6 6
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (6 6 (:REWRITE |(< 0 (- x))|))
                (6 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                (6 6
                   (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                (6 6 (:LINEAR <-OF-*-AND-*))
                (4 4
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (4 4 (:REWRITE |(< (- x) 0)|))
                (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                (2 2 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                (2 2 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                (2 2
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                (2 2 (:REWRITE DEFAULT-*-2))
                (2 2 (:REWRITE DEFAULT-*-1))
                (2 2 (:REWRITE |(- (* c x))|))
                (2 2 (:REWRITE |(* c (* d x))|))
                (1 1 (:REWRITE |(< (* x y) 0)|)))
(MOD-OF-*-LEMMA-ALT (96 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
                    (80 16
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                    (68 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                    (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                    (65 13
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                    (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (31 1 (:REWRITE <-OF-*-AND-0))
                    (30 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                    (24 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                    (16 16
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                    (16 16 (:REWRITE |(< (- x) (- y))|))
                    (14 14 (:REWRITE SIMPLIFY-SUMS-<))
                    (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                    (13 13
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                    (13 13 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                    (13 13
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                    (13 13
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                    (13 13 (:REWRITE DEFAULT-<-2))
                    (13 13 (:REWRITE DEFAULT-<-1))
                    (9 9
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                    (9 9 (:REWRITE DEFAULT-UNARY-/))
                    (7 7
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (7 7 (:REWRITE DEFAULT-*-2))
                    (7 7 (:REWRITE DEFAULT-*-1))
                    (7 7 (:REWRITE |(* c (* d x))|))
                    (6 6
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                    (6 6
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                    (6 6 (:REWRITE |(< 0 (- x))|))
                    (6 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                    (6 6
                       (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                    (6 6 (:LINEAR <-OF-*-AND-*))
                    (3 3
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                    (3 3 (:REWRITE |(< (- x) 0)|))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                    (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                    (2 2 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                    (2 2 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                    (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                    (2 2 (:REWRITE |(- (* c x))|))
                    (1 1 (:REWRITE |(< (* x y) 0)|)))
(INTEGERP-OF-MOD-OF-1
     (30 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (28 2 (:REWRITE CANCEL-FLOOR-+))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18 (:META META-INTEGERP-CORRECT))
     (16 2 (:REWRITE FLOOR-WHEN-<))
     (16 2 (:REWRITE DEFAULT-+-2))
     (14 1 (:REWRITE CANCEL-MOD-+))
     (12 3 (:REWRITE INTEGERP-OF-*))
     (12 2
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (11 11
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (11 11 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (11 11
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (11 11
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (11 11 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (11 11 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (11 11
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 11
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (11 11 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (11 11 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (11 11
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (11 11
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (11 11
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (11 11 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
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
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (8 2 (:REWRITE FLOOR-X-1))
     (8 2 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
     (8 1 (:REWRITE MOD-WHEN-<))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-*-2))
     (5 5 (:REWRITE DEFAULT-*-1))
     (4 2 (:REWRITE FLOOR-COMPLETION))
     (4 1 (:REWRITE MOD-X-1))
     (4 1 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE |(integerp (* c x))|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (2 2 (:REWRITE FLOOR-ZERO . 4))
     (2 2 (:REWRITE FLOOR-ZERO . 3))
     (2 2 (:REWRITE FLOOR-ZERO . 2))
     (2 2
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (2 2
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (2 2
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (2 2 (:REWRITE FLOOR-MINUS-WEAK))
     (2 2
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (2 2 (:REWRITE FLOOR-MINUS-2))
     (2 2 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (1 1 (:REWRITE MOD-ZERO . 3))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE MOD-X-Y-=-X . 4))
     (1 1 (:REWRITE MOD-X-Y-=-X . 3))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE |(+ 0 x)|)))
(MOD-CANCEL (169 169
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (169 169
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (169 169
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (169 169
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (112 3 (:REWRITE FLOOR-WHEN-<))
            (103 13
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (96 6 (:REWRITE DEFAULT-+-2))
            (92 3 (:REWRITE CANCEL-FLOOR-+))
            (66 2 (:REWRITE MOD-WHEN-<))
            (63 3
                (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
            (61 7 (:REWRITE DEFAULT-UNARY-MINUS))
            (51 15 (:REWRITE DEFAULT-*-2))
            (40 40
                (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
            (40 40 (:TYPE-PRESCRIPTION RATIONALP-MOD))
            (40 40
                (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
            (40 40
                (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
            (40 40 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
            (40 40
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
            (40 40
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
            (40 40 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
            (40 40 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
            (40 40
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
            (40 40
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
            (40 40
                (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
            (40 40 (:TYPE-PRESCRIPTION INTEGERP-MOD))
            (39 2 (:REWRITE FLOOR-X-1))
            (37 37
                (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
            (37 37
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
            (37 37
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
            (37 37
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
            (37 37
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
            (36 36 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
            (36 36
                (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
            (36 36
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
            (36 36
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
            (36 36
                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
            (36 36
                (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
            (36 2 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
            (35 2 (:REWRITE CANCEL-MOD-+))
            (30 5 (:REWRITE |(* (* x y) z)|))
            (28 10 (:REWRITE INTEGERP-OF-*))
            (28 7 (:REWRITE DEFAULT-UNARY-/))
            (27 3 (:REWRITE FLOOR-ZERO . 4))
            (27 3
                (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
            (27 3 (:REWRITE FLOOR-MINUS-WEAK))
            (27 3 (:REWRITE FLOOR-MINUS-2))
            (27 3 (:REWRITE FLOOR-CANCEL-*-WEAK))
            (24 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
            (21 1 (:REWRITE MOD-X-1))
            (20 8 (:REWRITE DEFAULT-<-1))
            (18 1 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
            (16 16 (:REWRITE REDUCE-INTEGERP-+))
            (16 16 (:REWRITE INTEGERP-MINUS-X))
            (16 16 (:META META-INTEGERP-CORRECT))
            (16 8 (:REWRITE SIMPLIFY-SUMS-<))
            (16 8
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
            (16 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
            (15 15
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (15 15 (:REWRITE DEFAULT-*-1))
            (14 2 (:REWRITE MOD-ZERO . 3))
            (14 2 (:REWRITE MOD-X-Y-=-X . 4))
            (14 2 (:REWRITE MOD-NEG))
            (14 2 (:REWRITE MOD-MINUS-2))
            (14 2 (:REWRITE MOD-CANCEL-*))
            (13 13 (:REWRITE |(equal (- x) (- y))|))
            (13 3 (:REWRITE FLOOR-COMPLETION))
            (11 3
                (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
            (11 3
                (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
            (10 10 (:REWRITE |(integerp (* c x))|))
            (10 6 (:REWRITE DEFAULT-+-1))
            (9 9
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
            (9 9 (:REWRITE |(equal (- x) 0)|))
            (8 8
               (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
            (8 8 (:REWRITE DEFAULT-<-2))
            (8 8 (:REWRITE |(< (- x) (- y))|))
            (8 4 (:REWRITE MOD-COMPLETION))
            (8 2 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
            (8 2 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
            (7 7
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
            (6 6
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (6 6 (:REWRITE |(+ c (+ d x))|))
            (6 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
            (6 6
               (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
            (6 6 (:LINEAR <-OF-*-AND-*))
            (5 5 (:DEFINITION NOT))
            (4 4 (:REWRITE |(equal (+ c x) d)|))
            (3 3 (:REWRITE FLOOR-ZERO . 3))
            (3 3 (:REWRITE FLOOR-ZERO . 2))
            (3 3
               (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
            (3 3 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
            (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
            (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
            (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
            (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
            (2 2 (:REWRITE MOD-ZERO . 2))
            (2 2 (:REWRITE MOD-X-Y-=-X . 3))
            (2 2 (:REWRITE MOD-X-Y-=-X . 2))
            (2 2 (:REWRITE |(* (- x) y)|))
            (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
            (1 1 (:REWRITE |(equal (+ d x) (+ c y))|))
            (1 1 (:REWRITE |(equal (+ c x) (+ d y))|))
            (1 1 (:REWRITE |(equal (* x y) 0)|))
            (1 1 (:REWRITE |(* c (* d x))|)))
(MOD-SUM-CASES (22455 63
                      (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
               (7490 84 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
               (7322 42 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
               (3809 170 (:REWRITE CANCEL-FLOOR-+))
               (2364 154 (:REWRITE DEFAULT-+-2))
               (1783 170 (:REWRITE FLOOR-ZERO . 4))
               (1783 170 (:REWRITE FLOOR-ZERO . 3))
               (1427 461 (:REWRITE DEFAULT-*-2))
               (1375 735
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (1300 170 (:REWRITE FLOOR-WHEN-<))
               (1224 732 (:REWRITE SIMPLIFY-SUMS-<))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (1211 1211
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (1206 730 (:REWRITE DEFAULT-<-2))
               (1147 1147
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (1147 1147
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (1147 1147
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (1056 273 (:REWRITE INTEGERP-OF-*))
               (988 38 (:LINEAR FLOOR-BOUNDS-3))
               (988 38 (:LINEAR FLOOR-BOUNDS-2))
               (850 170
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
               (735 735
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
               (735 735 (:REWRITE |(< (- x) (- y))|))
               (730 730 (:REWRITE DEFAULT-<-1))
               (678 454 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
               (678 454
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
               (572 572 (:REWRITE REDUCE-INTEGERP-+))
               (572 572 (:REWRITE INTEGERP-MINUS-X))
               (572 572 (:META META-INTEGERP-CORRECT))
               (461 461
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (461 461 (:REWRITE DEFAULT-*-1))
               (454 454
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
               (454 454
                    (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
               (454 454
                    (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
               (454 454
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
               (454 454
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
               (454 454
                    (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
               (454 454 (:TYPE-PRESCRIPTION INTEGERP-MOD))
               (454 454
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
               (446 392 (:REWRITE DEFAULT-UNARY-/))
               (398 398
                    (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
               (398 398
                    (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
               (396 36 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
               (394 154 (:REWRITE DEFAULT-+-1))
               (392 392
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
               (384 24
                    (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
               (336 24 (:DEFINITION NATP))
               (308 26 (:REWRITE MOD-ZERO . 2))
               (294 28 (:REWRITE DEFAULT-UNARY-MINUS))
               (289 19 (:REWRITE CANCEL-MOD-+))
               (280 28 (:LINEAR MOD-BOUNDS-1))
               (273 273 (:REWRITE |(integerp (* c x))|))
               (255 255
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (255 255 (:REWRITE |(< (- x) 0)|))
               (236 236
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (236 236 (:REWRITE |(< 0 (- x))|))
               (219 26 (:REWRITE MOD-X-Y-=-X . 4))
               (219 26 (:REWRITE MOD-X-Y-=-X . 3))
               (212 170 (:REWRITE FLOOR-ZERO . 2))
               (170 170
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
               (170 170
                    (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
               (170 170
                    (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
               (170 170 (:REWRITE FLOOR-MINUS-WEAK))
               (170 170
                    (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
               (170 170 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
               (170 170 (:REWRITE FLOOR-MINUS-2))
               (170 170 (:REWRITE FLOOR-COMPLETION))
               (170 170 (:REWRITE FLOOR-CANCEL-*-WEAK))
               (162 26 (:REWRITE MOD-WHEN-<))
               (160 14 (:LINEAR MOD-BOUND-LINEAR-ARG1))
               (154 154
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (143 26 (:REWRITE MOD-ZERO . 3))
               (140 14 (:LINEAR MOD-BOUND-LINEAR-ARG2))
               (126 14 (:REWRITE FLOOR-POSITIVE . 2))
               (116 116 (:REWRITE |(equal (- x) (- y))|))
               (98 14 (:LINEAR MOD-BOUNDS-3))
               (89 89 (:REWRITE |(equal (- x) 0)|))
               (84 84
                   (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
               (84 84 (:LINEAR <-OF-*-AND-*))
               (77 77
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (68 26 (:REWRITE MOD-X-Y-=-X . 2))
               (65 9 (:REWRITE |(< d (+ c x))|))
               (56 28 (:REWRITE |(equal (+ c x) d)|))
               (56 14 (:REWRITE <-OF-0-AND-FLOOR))
               (52 52 (:REWRITE MOD-COMPLETION))
               (48 48 (:REWRITE FOLD-CONSTS-IN-+))
               (48 48 (:REWRITE +-COMBINE-CONSTANTS))
               (42 42 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
               (42 42 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
               (42 42 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
               (42 42 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
               (37 19 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
               (37 19 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
               (33 5 (:REWRITE |(< d (+ c x y))|))
               (32 1 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
               (28 28 (:LINEAR MOD-BOUNDS-2))
               (27 13 (:REWRITE |(equal (+ c x y) d)|))
               (26 1 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG1))
               (24 24
                   (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
               (24 24 (:TYPE-PRESCRIPTION NATP))
               (22 14 (:REWRITE |(< (+ c x) d)|))
               (19 19 (:REWRITE MOD-NEG))
               (19 19 (:REWRITE MOD-MINUS-2))
               (19 19 (:REWRITE MOD-CANCEL-*))
               (19 19 (:REWRITE |(- (* c x))|))
               (15 7 (:REWRITE |(< (+ d x) (+ c y))|))
               (15 7 (:REWRITE |(< (+ c x) (+ d y))|))
               (14 14 (:REWRITE FLOOR-POSITIVE . 3))
               (14 14 (:REWRITE FLOOR-POSITIVE . 1))
               (12 12 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
               (12 12 (:REWRITE |(* c (* d x))|))
               (11 11 (:REWRITE |(equal (+ d x) (+ c y))|))
               (11 11 (:REWRITE |(equal (+ c x) (+ d y))|))
               (9 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
               (9 9
                  (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
               (7 7 (:REWRITE MOD-ZERO . 1))
               (7 7 (:REWRITE MOD-+-CANCEL-0-WEAK))
               (7 3 (:REWRITE |(< (+ c x y) d)|))
               (5 5 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
               (5 5
                  (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
               (1 1 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
               (1 1
                  (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
               (1 1
                  (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
               (1 1
                  (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS)))
(MOD-OF-MOD-WHEN-MULT
     (528586 223
             (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (488396 2422
             (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (103763 1297
             (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (100022 760 (:DEFINITION NATP))
     (43818 35849
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (43818 35849
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (43818 35849
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (43818 35849
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (43818 35849
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (43817 35848
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (43817 35848
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (43817 35848
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (43817 35848
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (41835 924 (:REWRITE FLOOR-WHEN-<))
     (35849 35849
            (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (35848 35848
            (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (34613 5005 (:REWRITE DEFAULT-<-2))
     (30253 68 (:REWRITE |(< (if a b c) x)|))
     (28561 319
            (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
     (23764 5662 (:REWRITE DEFAULT-*-2))
     (22177 1409 (:LINEAR FLOOR-BOUNDS-3))
     (20406 1409 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (15925 119 (:REWRITE CANCEL-MOD-+))
     (15726 256
            (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (13998 94 (:REWRITE <-OF-*-AND-0))
     (10008 617
            (:REWRITE RATIONALP-OF-+-WHEN-RATIONALP-ARG2))
     (9766 510 (:REWRITE DEFAULT-UNARY-MINUS))
     (9342 137 (:REWRITE MOD-WHEN-<))
     (9003 4185 (:REWRITE DEFAULT-UNARY-/))
     (7295 98
           (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
     (7285 7131
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (6543 6543
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (6543 6543
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (6543 6543
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5948 266
           (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (5942 4844
           (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (5662 5662
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5513 5513
           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (5437 5437 (:REWRITE |(< (- x) (- y))|))
     (5225 5005 (:REWRITE DEFAULT-<-1))
     (4844 4844
           (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (4844 4844 (:LINEAR <-OF-*-AND-*))
     (4701 4701
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (4701 4701
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (4701 4701
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (4571 1297
           (:LINEAR MY-FLOOR-LOWER-BOUND-ALT-LINEAR))
     (4571 1297
           (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
     (4185 4185
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3520 2422
           (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (3520 2422
           (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (2492 246
           (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (2422 2422
           (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (2422 2422
           (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (2345 2345
           (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (2120 2120 (:REWRITE |(integerp (* c x))|))
     (2073 1029 (:REWRITE FLOOR-MINUS-WEAK))
     (2073 1029 (:REWRITE FLOOR-MINUS-2))
     (2073 1029 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (1708 924
           (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (1708 924
           (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (1619 1023 (:REWRITE FLOOR-ZERO . 2))
     (1505 1505 (:REWRITE |(< (- x) 0)|))
     (1497 1497 (:REWRITE |(equal (- x) (- y))|))
     (1454 1454
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1378 1378
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1366 1366 (:REWRITE |(< 0 (- x))|))
     (1350 1350 (:REWRITE |(equal (- x) 0)|))
     (1345 1345 (:REWRITE |(* c (* d x))|))
     (1288 1288 (:TYPE-PRESCRIPTION NATP))
     (1271 131 (:REWRITE MOD-ZERO . 2))
     (1268 1268
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1251 1251
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (1197 1197
           (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (1000 40 (:REWRITE <-OF-FLOOR-AND-0))
     (924 924
          (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (924 924 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (897 621 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (881 131 (:REWRITE MOD-ZERO . 3))
     (809 809 (:REWRITE |(< (+ c x) d)|))
     (771 131 (:REWRITE MOD-X-Y-=-X . 4))
     (766 626
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (766 626
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (766 626
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (766 626
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (761 621
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (761 621
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (761 621
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (761 621
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (761 621 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (727 587
          (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (621 621
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (615 615
          (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (615 615
          (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (575 119 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (575 119 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (541 131 (:REWRITE MOD-X-Y-=-X . 3))
     (474 474 (:REWRITE |(- (* c x))|))
     (439 131 (:REWRITE MOD-X-Y-=-X . 2))
     (427 119 (:REWRITE MOD-NEG))
     (427 119 (:REWRITE MOD-MINUS-2))
     (427 119 (:REWRITE MOD-CANCEL-*))
     (412 60 (:LINEAR MOD-BOUNDS-2))
     (412 60 (:LINEAR MOD-BOUNDS-1))
     (388 262 (:REWRITE MOD-COMPLETION))
     (369 369 (:REWRITE |(< d (+ c x))|))
     (369 71
          (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
     (319 319 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
     (319 319
          (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
     (316 316
          (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (316 316
          (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (268 268
          (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (224 20 (:REWRITE MOD-SUM-CASES))
     (206 30 (:LINEAR MOD-BOUNDS-3))
     (206 30 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (206 30 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (167 167 (:REWRITE |(equal (+ c x) d)|))
     (155 155 (:REWRITE FOLD-CONSTS-IN-+))
     (155 155 (:REWRITE +-COMBINE-CONSTANTS))
     (109 21 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (102 102 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (82 82 (:REWRITE FLOOR-ZERO . 1))
     (82 82 (:REWRITE EQUAL-OF-0-AND-FLOOR))
     (52 52 (:REWRITE FLOOR-MINUS-ARG1-HACK))
     (51 51
         (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (51 51
         (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (40 40 (:REWRITE FLOOR-POSITIVE . 3))
     (40 40 (:REWRITE FLOOR-POSITIVE . 2))
     (40 40 (:REWRITE FLOOR-POSITIVE . 1))
     (40 40 (:REWRITE FLOOR-NONPOSITIVE-2))
     (40 40 (:REWRITE FLOOR-NONPOSITIVE-1))
     (40 40 (:REWRITE FLOOR-NONNEGATIVE-2))
     (40 40 (:REWRITE FLOOR-NONNEGATIVE-1))
     (40 40 (:REWRITE FLOOR-NEGATIVE . 3))
     (40 40 (:REWRITE FLOOR-NEGATIVE . 2))
     (40 40 (:REWRITE FLOOR-NEGATIVE . 1))
     (40 40
         (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
     (40 40 (:REWRITE <-OF-FLOOR-AND-0-2))
     (40 40 (:REWRITE <-OF-0-AND-FLOOR))
     (35 7 (:REWRITE |(* (if a b c) x)|))
     (28 28 (:REWRITE |(equal (+ c x y) d)|))
     (13 13 (:REWRITE MOD-ZERO . 1))
     (13 13 (:REWRITE |(< (+ c x y) d)|))
     (8 8 (:REWRITE |(< (+ d x) (+ c y))|))
     (8 8 (:REWRITE |(< (+ c x) (+ d y))|))
     (7 7 (:REWRITE |(equal (+ d x) (+ c y))|))
     (7 7 (:REWRITE |(equal (+ c x) (+ d y))|))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (3 3 (:REWRITE MOD-X-Y-=-X . 1))
     (3 3 (:REWRITE EQUAL-OF-MOD-SAME-ARG1)))
(MOD-OF-*-OF-MOD (3146 28 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                 (2687 13 (:REWRITE <-OF-*-AND-0))
                 (1431 52 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                 (1079 11 (:REWRITE MOD-X-Y-=-X . 3))
                 (920 644 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (803 667
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (779 667
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (667 667
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (667 667
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                 (616 616
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                 (616 616
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                 (613 11 (:REWRITE MOD-ZERO . 3))
                 (512 56 (:LINEAR MOD-BOUNDS-2))
                 (512 56 (:LINEAR MOD-BOUNDS-1))
                 (440 272 (:REWRITE DEFAULT-<-2))
                 (403 11 (:REWRITE MOD-X-Y-=-X . 4))
                 (401 401
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (368 272 (:REWRITE DEFAULT-<-1))
                 (306 306
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                 (302 302 (:REWRITE |(< (- x) (- y))|))
                 (266 6 (:REWRITE |(equal (* x y) 0)|))
                 (256 28 (:LINEAR MOD-BOUND-LINEAR-ARG2))
                 (196 28 (:LINEAR MOD-BOUNDS-3))
                 (164 108 (:REWRITE DEFAULT-*-2))
                 (158 62
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (140 15 (:REWRITE INTEGERP-OF-*))
                 (134 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (134 62
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (133 133
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                 (127 127 (:REWRITE |(< 0 (- x))|))
                 (125 125
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                 (122 104 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                 (122 104
                      (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                 (121 11 (:REWRITE MOD-ZERO . 2))
                 (117 117 (:REWRITE |(< (- x) 0)|))
                 (115 115
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                 (108 108
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (108 108 (:REWRITE DEFAULT-*-1))
                 (104 104 (:LINEAR <-OF-*-AND-*))
                 (78 46 (:META META-INTEGERP-CORRECT))
                 (70 52 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                 (70 52 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                 (65 57 (:REWRITE DEFAULT-+-2))
                 (62 62 (:REWRITE |(equal (- x) (- y))|))
                 (62 50 (:REWRITE DEFAULT-UNARY-/))
                 (61 52 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                 (61 52 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                 (60 60
                     (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                 (60 60
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                 (60 60 (:REWRITE |(equal (- x) 0)|))
                 (57 57
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (57 57 (:REWRITE DEFAULT-+-1))
                 (52 4 (:REWRITE MOD-+-CANCEL-0-WEAK))
                 (50 50
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                 (46 46 (:REWRITE INTEGERP-MINUS-X))
                 (46 22 (:REWRITE MOD-COMPLETION))
                 (42 42
                     (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                 (42 6 (:REWRITE MOD-POSITIVE . 3))
                 (42 6 (:REWRITE MOD-NONPOSITIVE))
                 (42 6 (:REWRITE MOD-NONNEGATIVE))
                 (42 6 (:REWRITE MOD-NEGATIVE . 3))
                 (35 11 (:REWRITE MOD-NEG))
                 (35 11 (:REWRITE MOD-CANCEL-*))
                 (30 6 (:REWRITE MOD-POSITIVE . 2))
                 (30 6 (:REWRITE MOD-NEGATIVE . 2))
                 (27 15 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                 (27 15 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                 (24 24 (:REWRITE |(* c (* d x))|))
                 (19 19 (:REWRITE DEFAULT-UNARY-MINUS))
                 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
                 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                 (15 15 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
                 (15 15 (:REWRITE |(integerp (* c x))|))
                 (11 11 (:REWRITE MOD-X-Y-=-X . 2))
                 (11 11 (:REWRITE MOD-MINUS-2))
                 (10 10 (:REWRITE |(< (+ c x) d)|))
                 (9 9 (:REWRITE |(< d (+ c x))|))
                 (6 6 (:REWRITE MOD-POSITIVE . 1))
                 (6 6 (:REWRITE MOD-NEGATIVE . 1))
                 (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                 (4 4
                    (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                 (4 4 (:REWRITE |(- (* c x))|))
                 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                 (3 3
                    (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
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
                 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                 (3 3
                    (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                 (2 2 (:REWRITE MOD-ZERO . 1))
                 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                 (2 2 (:REWRITE +-COMBINE-CONSTANTS))
                 (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
                 (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
                 (2 2 (:REWRITE |(< (+ c x y) d)|))
                 (1 1
                    (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT)))
(MOD-OF-*-OF-MOD-2 (1098 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                   (915 3 (:REWRITE <-OF-*-AND-0))
                   (168 12 (:LINEAR MOD-BOUNDS-2))
                   (168 12 (:LINEAR MOD-BOUNDS-1))
                   (142 142
                        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                   (142 142
                        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                   (142 142 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (142 142
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (142 142
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (142 142
                        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (142 142
                        (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                   (142 142
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (142 142
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (137 65 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (113 65 (:REWRITE SIMPLIFY-SUMS-<))
                   (113 65
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (86 62 (:REWRITE DEFAULT-<-2))
                   (86 62 (:REWRITE DEFAULT-<-1))
                   (84 6 (:LINEAR MOD-BOUND-LINEAR-ARG2))
                   (74 3 (:REWRITE MOD-X-Y-=-X . 3))
                   (66 6 (:LINEAR MOD-BOUNDS-3))
                   (65 65
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (65 65 (:REWRITE |(< (- x) (- y))|))
                   (44 3 (:REWRITE MOD-ZERO . 3))
                   (35 3 (:REWRITE MOD-X-Y-=-X . 4))
                   (35 3 (:REWRITE MOD-WHEN-<))
                   (30 30
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                   (30 30
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                   (30 30 (:REWRITE |(< 0 (- x))|))
                   (30 30 (:REWRITE |(< (- x) 0)|))
                   (28 7 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                   (22 22
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (20 2 (:REWRITE MOD-POSITIVE . 3))
                   (20 2 (:REWRITE MOD-NONPOSITIVE))
                   (20 2 (:REWRITE MOD-NONNEGATIVE))
                   (20 2 (:REWRITE MOD-NEGATIVE . 3))
                   (17 17
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                   (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (17 17
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (17 17
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (17 17 (:REWRITE |(equal (- x) 0)|))
                   (17 17 (:REWRITE |(equal (- x) (- y))|))
                   (16 16
                       (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                   (15 3 (:REWRITE DEFAULT-*-2))
                   (14 14 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                   (14 14
                       (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                   (14 14 (:LINEAR <-OF-*-AND-*))
                   (14 2 (:REWRITE MOD-POSITIVE . 2))
                   (14 2 (:REWRITE MOD-NEGATIVE . 2))
                   (13 1 (:REWRITE |(equal (* x y) 0)|))
                   (10 10
                       (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                   (9 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                   (9 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                   (9 3 (:REWRITE MOD-ZERO . 2))
                   (9 3 (:REWRITE CANCEL-MOD-+))
                   (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                   (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                   (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                   (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                   (6 6 (:REWRITE MOD-COMPLETION))
                   (3 3 (:REWRITE REDUCE-INTEGERP-+))
                   (3 3
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (3 3 (:REWRITE MOD-X-Y-=-X . 2))
                   (3 3 (:REWRITE MOD-NEG))
                   (3 3 (:REWRITE MOD-MINUS-2))
                   (3 3 (:REWRITE MOD-CANCEL-*))
                   (3 3 (:REWRITE INTEGERP-MINUS-X))
                   (3 3 (:REWRITE DEFAULT-*-1))
                   (3 3 (:REWRITE |(< (* x y) 0)|))
                   (3 3 (:META META-INTEGERP-CORRECT))
                   (2 2 (:REWRITE MOD-POSITIVE . 1))
                   (2 2 (:REWRITE MOD-NEGATIVE . 1))
                   (1 1 (:REWRITE |(< 0 (* x y))|)))
(MOD-MULT-LEMMA (424 268 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (336 268
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (320 268
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (304 304
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (268 268
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (268 268
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (258 8 (:LINEAR MOD-BOUND-LINEAR-ARG1))
                (255 255
                     (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                (255 255
                     (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                (170 7 (:REWRITE MOD-X-Y-=-X . 3))
                (165 165
                     (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (161 161 (:REWRITE |(< (- x) (- y))|))
                (160 16 (:LINEAR MOD-BOUNDS-2))
                (160 16 (:LINEAR MOD-BOUNDS-1))
                (153 7 (:REWRITE MOD-ZERO . 3))
                (142 142 (:REWRITE DEFAULT-<-2))
                (142 142 (:REWRITE DEFAULT-<-1))
                (130 32 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                (125 53 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (125 53
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (125 53
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (83 83
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (82 64
                    (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                (80 8 (:LINEAR MOD-BOUND-LINEAR-ARG2))
                (74 66 (:REWRITE DEFAULT-+-2))
                (68 32 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                (66 66
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (66 66 (:REWRITE DEFAULT-+-1))
                (65 65
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (65 65 (:REWRITE DEFAULT-*-2))
                (65 65 (:REWRITE DEFAULT-*-1))
                (64 64 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                (64 64 (:LINEAR <-OF-*-AND-*))
                (64 46 (:REWRITE DEFAULT-UNARY-/))
                (60 60 (:REWRITE |(< 0 (- x))|))
                (58 58
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (56 8 (:LINEAR MOD-BOUNDS-3))
                (53 53 (:REWRITE |(equal (- x) (- y))|))
                (51 51 (:REWRITE |(< (- x) 0)|))
                (50 50
                    (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                (50 50
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (50 50 (:REWRITE |(equal (- x) 0)|))
                (49 49
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (46 46
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (44 44
                    (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                (41 1 (:REWRITE <-OF-*-AND-0))
                (40 8 (:REWRITE |(* y (* x z))|))
                (40 4 (:REWRITE MOD-+-CANCEL-0-WEAK))
                (36 12 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                (36 12 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                (34 2 (:REWRITE |(* x (+ y z))|))
                (32 32 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                (32 32 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                (32 32 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                (31 7 (:REWRITE MOD-ZERO . 2))
                (25 25 (:REWRITE |(< (+ c x) d)|))
                (23 23 (:REWRITE INTEGERP-MINUS-X))
                (23 23 (:META META-INTEGERP-CORRECT))
                (22 8 (:REWRITE MOD-CANCEL-*))
                (20 2 (:DEFINITION POSP))
                (19 19 (:REWRITE DEFAULT-UNARY-MINUS))
                (17 17
                    (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                (17 17
                    (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                (14 14 (:REWRITE MOD-COMPLETION))
                (9 9 (:REWRITE |(< d (+ c x))|))
                (8 8 (:REWRITE MOD-NEG))
                (8 8 (:REWRITE MOD-MINUS-2))
                (8 8 (:REWRITE |(* c (* d x))|))
                (7 7 (:REWRITE MOD-X-Y-=-X . 2))
                (5 5 (:REWRITE |(< (+ c x y) d)|))
                (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                (4 4
                   (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                (4 4 (:REWRITE +-COMBINE-CONSTANTS))
                (4 4 (:REWRITE |(- (* c x))|))
                (4 1 (:REWRITE INTEGERP-OF-*))
                (4 1 (:REWRITE INSERT-0-*))
                (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (3 3
                   (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                (3 3
                   (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
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
                (3 3
                   (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                (3 3
                   (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                (3 3 (:REWRITE |(equal (+ c x) d)|))
                (2 2 (:TYPE-PRESCRIPTION POSP))
                (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
                (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
                (1 1
                   (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
                (1 1 (:REWRITE INSERT-0-X-Y))
                (1 1 (:REWRITE |(integerp (* c x))|)))
(MOD-SAME (26 1
              (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
          (22 2
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
          (22 1 (:REWRITE CANCEL-FLOOR-+))
          (20 2 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
          (18 2 (:REWRITE |(* x (/ x))|))
          (16 2 (:REWRITE DEFAULT-UNARY-/))
          (10 10
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
          (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (10 10
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (10 10
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (10 10 (:REWRITE |(equal (- x) 0)|))
          (10 10 (:REWRITE |(equal (- x) (- y))|))
          (9 9 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
          (9 9 (:TYPE-PRESCRIPTION RATIONALP-MOD))
          (9 9
             (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
          (9 9
             (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
          (9 9 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
          (9 9 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
          (9 9 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
          (9 9 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
          (9 9 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
          (9 9 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
          (9 9 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
          (9 9 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
          (9 9
             (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
          (9 9 (:TYPE-PRESCRIPTION INTEGERP-MOD))
          (8 1 (:REWRITE MOD-WHEN-<))
          (8 1 (:REWRITE FLOOR-WHEN-<))
          (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
          (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
          (7 1 (:REWRITE CANCEL-MOD-+))
          (4 4 (:LINEAR MOD-BOUNDS-2))
          (4 4 (:LINEAR MOD-BOUNDS-1))
          (3 3 (:DEFINITION NOT))
          (2 2 (:REWRITE SIMPLIFY-SUMS-<))
          (2 2
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
          (2 2
             (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
          (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
          (2 2
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
          (2 2 (:REWRITE MOD-COMPLETION))
          (2 2 (:REWRITE DEFAULT-<-2))
          (2 2 (:REWRITE DEFAULT-<-1))
          (2 2 (:REWRITE |(< (- x) (- y))|))
          (2 2 (:REWRITE |(* a (/ a))|))
          (2 2 (:LINEAR MOD-BOUNDS-3))
          (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
          (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
          (2 1 (:REWRITE FLOOR-COMPLETION))
          (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
          (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (1 1
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (1 1 (:REWRITE MOD-ZERO . 3))
          (1 1 (:REWRITE MOD-ZERO . 2))
          (1 1 (:REWRITE MOD-X-Y-=-X . 4))
          (1 1 (:REWRITE MOD-X-Y-=-X . 3))
          (1 1 (:REWRITE MOD-X-Y-=-X . 2))
          (1 1 (:REWRITE MOD-NEG))
          (1 1 (:REWRITE MOD-MINUS-2))
          (1 1 (:REWRITE MOD-CANCEL-*))
          (1 1 (:REWRITE FLOOR-ZERO . 4))
          (1 1 (:REWRITE FLOOR-ZERO . 3))
          (1 1 (:REWRITE FLOOR-ZERO . 2))
          (1 1
             (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
          (1 1
             (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
          (1 1
             (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
          (1 1 (:REWRITE FLOOR-MINUS-WEAK))
          (1 1
             (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
          (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
          (1 1 (:REWRITE FLOOR-MINUS-2))
          (1 1 (:REWRITE FLOOR-CANCEL-*-WEAK))
          (1 1
             (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
          (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
          (1 1 (:REWRITE DEFAULT-+-2))
          (1 1 (:REWRITE DEFAULT-+-1))
          (1 1 (:REWRITE |(equal (+ c x) d)|))
          (1 1 (:REWRITE |(+ 0 x)|)))
(MOD-WHEN-NOT-ACL2-NUMBERP-ARG1 (5 5 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                                (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                                (5 5
                                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                                (5 5
                                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                                (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                                (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                                (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                                (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                                (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                                (5 5 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                                (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                                (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                                (5 5
                                   (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                                (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD)))
(MOD-WHEN-NOT-ACL2-NUMBERP-ARG2
     (19 19
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (19 19 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (19 19
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (19 19
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (19 19 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (19 19 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (19 19
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (19 19
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (19 19 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (19 19 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (19 19
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (19 19
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (19 19
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (19 19 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (16 1 (:REWRITE MOD-WHEN-<))
     (10 2 (:REWRITE DEFAULT-<-2))
     (5 1 (:REWRITE CANCEL-MOD-+))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 1 (:REWRITE |(* y x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE MOD-ZERO . 3))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE MOD-X-Y-=-X . 4))
     (1 1 (:REWRITE MOD-X-Y-=-X . 3))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE DEFAULT-UNARY-/))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE |(< (- x) 0)|))
     (1 1 (:REWRITE |(* 0 x)|)))
(MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2
     (27 27
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (27 27 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (27 27
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (27 27
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (27 27
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (27 27
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (27 27
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (25 1 (:REWRITE CANCEL-FLOOR-+))
     (24 1
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (14 2 (:REWRITE DEFAULT-UNARY-/))
     (8 1 (:REWRITE MOD-WHEN-<))
     (8 1 (:REWRITE FLOOR-WHEN-<))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (7 1 (:REWRITE CANCEL-MOD-+))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (5 5 (:REWRITE |(equal (- x) 0)|))
     (4 4 (:LINEAR MOD-BOUNDS-2))
     (4 4 (:LINEAR MOD-BOUNDS-1))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:LINEAR MOD-BOUNDS-3))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (2 1 (:REWRITE FLOOR-COMPLETION))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE MOD-ZERO . 3))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE MOD-X-Y-=-X . 4))
     (1 1 (:REWRITE MOD-X-Y-=-X . 3))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE INTEGERP-OF-*))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE FLOOR-ZERO . 4))
     (1 1 (:REWRITE FLOOR-ZERO . 3))
     (1 1 (:REWRITE FLOOR-ZERO . 2))
     (1 1
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (1 1
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (1 1 (:REWRITE FLOOR-MINUS-WEAK))
     (1 1
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (1 1 (:REWRITE FLOOR-MINUS-2))
     (1 1 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE |(integerp (* c x))|))
     (1 1 (:REWRITE |(equal (+ c x) d)|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(+ 0 x)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (80 16
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (80 16
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (80 16
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (75 3 (:REWRITE DEFAULT-+-2))
     (50 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (29 5 (:REWRITE DEFAULT-*-2))
     (27 27
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (27 27
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (27 27
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (27 27
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (27 27
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (27 27
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (27 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (23 1 (:REWRITE CANCEL-MOD-+))
     (23 1 (:REWRITE CANCEL-FLOOR-+))
     (22 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (21 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (19 1
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (18 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (13 4 (:REWRITE INTEGERP-OF-*))
     (13 1 (:REWRITE DEFAULT-NUMERATOR))
     (13 1 (:REWRITE DEFAULT-DENOMINATOR))
     (8 1 (:REWRITE MOD-WHEN-<))
     (8 1 (:REWRITE FLOOR-WHEN-<))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (7 4 (:REWRITE DEFAULT-UNARY-/))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-*-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE |(integerp (* c x))|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:LINEAR MOD-BOUNDS-2))
     (4 4 (:LINEAR MOD-BOUNDS-1))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (2 2
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(equal (+ c x) d)|))
     (2 2 (:REWRITE |(< (- x) 0)|))
     (2 2 (:LINEAR MOD-BOUNDS-3))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (2 1 (:REWRITE FLOOR-COMPLETION))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (1 1 (:REWRITE MOD-ZERO . 3))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE MOD-X-Y-=-X . 4))
     (1 1 (:REWRITE MOD-X-Y-=-X . 3))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE FLOOR-ZERO . 4))
     (1 1 (:REWRITE FLOOR-ZERO . 3))
     (1 1 (:REWRITE FLOOR-ZERO . 2))
     (1 1
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (1 1
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (1 1
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (1 1 (:REWRITE FLOOR-MINUS-WEAK))
     (1 1
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (1 1 (:REWRITE FLOOR-MINUS-2))
     (1 1 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (1 1 (:REWRITE |(- (* c x))|)))
(FLOOR-OF---SPECIAL-CASE
     (545 8
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (192 192
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (192 192
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (192 192
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (88 8 (:DEFINITION NFIX))
     (62 23 (:REWRITE DEFAULT-+-2))
     (54 22 (:REWRITE SIMPLIFY-SUMS-<))
     (54 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (54 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (54 22 (:REWRITE DEFAULT-<-1))
     (47 20 (:REWRITE DEFAULT-UNARY-MINUS))
     (40 8 (:DEFINITION IFIX))
     (31 23 (:REWRITE DEFAULT-+-1))
     (28 6 (:REWRITE DEFAULT-DENOMINATOR))
     (26 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (26 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (25 25
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (25 25 (:REWRITE |(< (- x) (- y))|))
     (23 23
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (23 23 (:REWRITE NORMALIZE-ADDENDS))
     (23 8 (:REWRITE INTEGERP-OF-*))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (22 22
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (22 22 (:REWRITE DEFAULT-UNARY-/))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-*-2))
     (22 22 (:REWRITE DEFAULT-*-1))
     (18 6 (:REWRITE DEFAULT-NUMERATOR))
     (16 16 (:META META-INTEGERP-CORRECT))
     (16 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (9 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
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
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (9 9
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (8 8 (:REWRITE |(integerp (* c x))|))
     (8 4 (:REWRITE |(equal (+ c x) d)|))
     (6 2 (:REWRITE |(equal (+ d x) (+ c y))|))
     (6 2 (:REWRITE |(equal (+ c x) (+ d y))|))
     (4 4 (:REWRITE |(< 0 (- x))|))
     (4 4 (:REWRITE |(- (* c x))|))
     (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (4 4
        (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (4 4 (:LINEAR <-OF-*-AND-*))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (3 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (1 1 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
     (1 1 (:REWRITE EQUAL-OF---AND-CONSTANT))
     (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (1 1 (:REWRITE <-OF-*-AND-0))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(MOD-OF-MINUS-ARG1
     (8745 24 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (3967 30 (:LINEAR FLOOR-BOUNDS-1))
     (1741 15 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (989 989
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (771 111 (:REWRITE DEFAULT-+-2))
     (570 332 (:REWRITE DEFAULT-*-2))
     (520 306 (:REWRITE DEFAULT-<-2))
     (519 519 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (519 519 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (519 519
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (506 54 (:REWRITE FLOOR-ZERO . 4))
     (504 54 (:REWRITE FLOOR-ZERO . 3))
     (490 15 (:LINEAR FLOOR-BOUNDS-3))
     (427 112 (:REWRITE INTEGERP-OF-*))
     (420 15 (:LINEAR FLOOR-BOUNDS-2))
     (389 53 (:REWRITE FLOOR-WHEN-<))
     (336 336
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (333 333
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (332 332 (:REWRITE |(< (- x) (- y))|))
     (329 157 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (306 306 (:REWRITE DEFAULT-<-1))
     (294 284 (:REWRITE DEFAULT-UNARY-/))
     (284 284
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (277 277 (:META META-INTEGERP-CORRECT))
     (272 15
          (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (262 46
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (242 15 (:DEFINITION NATP))
     (201 201
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (185 54
          (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (185 15 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (185 11 (:REWRITE CANCEL-MOD-+))
     (157 157
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (157 157
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (157 157
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (157 157
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (157 157
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (157 157
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (157 157
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (157 157
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (157 157
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (157 157 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (150 15
          (:LINEAR MY-FLOOR-LOWER-BOUND-ALT-LINEAR))
     (150 15
          (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
     (126 16 (:REWRITE MOD-ZERO . 2))
     (116 116
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (116 12 (:LINEAR MOD-BOUNDS-3))
     (112 112 (:REWRITE |(integerp (* c x))|))
     (111 111
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (111 111 (:REWRITE DEFAULT-+-1))
     (110 17 (:REWRITE MOD-WHEN-<))
     (109 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
     (104 24 (:LINEAR MOD-BOUNDS-2))
     (104 24 (:LINEAR MOD-BOUNDS-1))
     (100 16 (:REWRITE MOD-X-Y-=-X . 4))
     (98 98
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (96 96
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (96 16 (:REWRITE MOD-X-Y-=-X . 3))
     (94 41 (:REWRITE RATIONALP-OF--))
     (87 87 (:REWRITE |(- (* c x))|))
     (70 68 (:REWRITE FLOOR-MINUS-2))
     (70 68 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (60 16 (:REWRITE MOD-ZERO . 3))
     (56 12 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (55 53
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (55 53 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (54 54 (:REWRITE FLOOR-ZERO . 2))
     (54 54 (:REWRITE FLOOR-COMPLETION))
     (53 53
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (53 53
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (53 53
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (52 12 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (48 48 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (48 48
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (48 48 (:LINEAR <-OF-*-AND-*))
     (42 42
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (32 32 (:REWRITE MOD-COMPLETION))
     (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (24 18
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (24 18
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (18 16 (:REWRITE MOD-X-Y-=-X . 2))
     (17 17
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (16 16 (:REWRITE |(equal (+ c x) d)|))
     (16 11 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (16 11 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (15 15 (:TYPE-PRESCRIPTION NATP))
     (15 11 (:REWRITE MOD-NEG))
     (15 11 (:REWRITE MOD-MINUS-2))
     (15 11 (:REWRITE MOD-CANCEL-*))
     (12 12
         (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (12 12
         (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (7 7 (:REWRITE |(< (+ c x) d)|))
     (7 5 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (5 5 (:REWRITE MOD-ZERO . 1))
     (5 5 (:REWRITE FOLD-CONSTS-IN-+))
     (5 5 (:REWRITE +-COMBINE-CONSTANTS))
     (5 5 (:REWRITE |(< d (+ c x))|))
     (3 3 (:REWRITE |(* c (* d x))|))
     (3 1 (:REWRITE EQUAL-OF-0-AND-FLOOR))
     (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
     (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
     (2 2 (:REWRITE |(< (+ c x y) d)|))
     (1 1
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (1 1 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
     (1 1 (:REWRITE EQUAL-OF---AND-CONSTANT))
     (1 1 (:REWRITE |(equal (+ d x) (+ c y))|))
     (1 1 (:REWRITE |(equal (+ c x) (+ d y))|))
     (1 1 (:REWRITE |(equal (+ c x y) d)|)))
(MOD-OF-MINUS-ARG2
     (270 106 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (107 107
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (107 107
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (107 107
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (107 107
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (106 106
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (106 106
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (106 106
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (106 106
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (106 106
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (106 106 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (98 4 (:LINEAR MOD-BOUNDS-3))
     (81 4 (:REWRITE CANCEL-MOD-+))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (64 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (55 11 (:REWRITE |(< (- x) 0)|))
     (44 8 (:LINEAR MOD-BOUNDS-2))
     (44 8 (:LINEAR MOD-BOUNDS-1))
     (43 14 (:REWRITE DEFAULT-UNARY-MINUS))
     (42 3 (:REWRITE DEFAULT-+-2))
     (35 5 (:REWRITE MOD-WHEN-<))
     (26 26
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (26 26 (:REWRITE |(< (- x) (- y))|))
     (25 7 (:REWRITE INTEGERP-OF-*))
     (25 3 (:REWRITE MOD-ZERO . 2))
     (23 3 (:REWRITE MOD-X-Y-=-X . 4))
     (23 3 (:REWRITE MOD-X-Y-=-X . 3))
     (22 22 (:REWRITE SIMPLIFY-SUMS-<))
     (22 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (22 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-<-1))
     (22 4 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (20 2 (:REWRITE |(* (- x) y)|))
     (17 17 (:META META-INTEGERP-CORRECT))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (12 12
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (12 12 (:REWRITE |(< 0 (- x))|))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (9 9
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (9 9 (:REWRITE DEFAULT-UNARY-/))
     (9 9 (:REWRITE DEFAULT-*-2))
     (9 9 (:REWRITE DEFAULT-*-1))
     (9 3 (:REWRITE MOD-ZERO . 3))
     (8 8 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (7 7 (:REWRITE |(integerp (* c x))|))
     (6 6 (:REWRITE MOD-COMPLETION))
     (5 5
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (4 4 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (4 4 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (4 4 (:REWRITE MOD-CANCEL-*))
     (4 4 (:REWRITE |(- (* c x))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE MOD-X-Y-=-X . 2))
     (3 3 (:REWRITE MOD-NEG))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE |(equal (- x) 0)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK)))
(MOD-WHEN-MULTIPLE (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                   (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (1 1
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)))
(MOD-OF-+-OF-MOD-ARG1
     (60480 192
            (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (10660 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (10460 60 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (9508 1908 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (9508 1908
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (9382 494
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8920 80 (:LINEAR FLOOR-BOUNDS-1))
     (8374 75 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (7696 7696
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (7696 7696
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (7696 7696
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7064 420 (:REWRITE MOD-ZERO . 2))
     (6886 313 (:REWRITE CANCEL-FLOOR-+))
     (6513 399 (:REWRITE DEFAULT-+-2))
     (4916 1594 (:REWRITE DEFAULT-*-2))
     (4105 1270 (:REWRITE INTEGERP-OF-*))
     (3742 494
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3640 40 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (3510 2012
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3440 420 (:REWRITE MOD-X-Y-=-X . 4))
     (3440 420 (:REWRITE MOD-X-Y-=-X . 3))
     (3344 152 (:REWRITE CANCEL-MOD-+))
     (3142 454 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3043 313 (:REWRITE FLOOR-ZERO . 4))
     (3043 313 (:REWRITE FLOOR-ZERO . 3))
     (2915 1993 (:REWRITE SIMPLIFY-SUMS-<))
     (2774 1990 (:REWRITE DEFAULT-<-2))
     (2649 75 (:LINEAR MOD-BOUNDS-3))
     (2456 174 (:REWRITE DEFAULT-UNARY-MINUS))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (2405 2405
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2405 2273 (:META META-INTEGERP-CORRECT))
     (2273 2273 (:REWRITE REDUCE-INTEGERP-+))
     (2273 2273 (:REWRITE INTEGERP-MINUS-X))
     (2232 420 (:REWRITE MOD-ZERO . 3))
     (2224 313 (:REWRITE FLOOR-WHEN-<))
     (2142 1990 (:REWRITE DEFAULT-<-1))
     (2012 2012
           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (2012 2012 (:REWRITE |(< (- x) (- y))|))
     (1980 1908
           (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (1980 1908 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (1908 1908
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1908 1908
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1908 1908
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1908 1908
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1680 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1594 1594
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1594 1594 (:REWRITE DEFAULT-*-1))
     (1565 313
           (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (1384 1384
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1384 1384 (:REWRITE DEFAULT-UNARY-/))
     (1357 1357
           (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1270 1270 (:REWRITE |(integerp (* c x))|))
     (1147 399 (:REWRITE DEFAULT-+-1))
     (1040 40 (:LINEAR FLOOR-BOUNDS-3))
     (1040 40 (:LINEAR FLOOR-BOUNDS-2))
     (1034 14
           (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (964 452
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (964 452
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (964 452
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (926 18 (:REWRITE |(* (+ x y) z)|))
     (840 840 (:REWRITE MOD-COMPLETION))
     (728 728
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (728 728 (:REWRITE |(< (- x) 0)|))
     (596 596
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (596 596 (:REWRITE |(< 0 (- x))|))
     (494 494 (:REWRITE |(equal (- x) (- y))|))
     (454 454 (:REWRITE |(equal (- x) 0)|))
     (452 452
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (440 40 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (420 420 (:REWRITE MOD-X-Y-=-X . 2))
     (414 414
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (399 399
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (320 20
          (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (313 313 (:REWRITE FLOOR-ZERO . 2))
     (313 313
          (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (313 313
          (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (313 313
          (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (313 313 (:REWRITE FLOOR-MINUS-WEAK))
     (313 313
          (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (313 313 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (313 313 (:REWRITE FLOOR-MINUS-2))
     (313 313 (:REWRITE FLOOR-COMPLETION))
     (313 313 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (280 20 (:DEFINITION NATP))
     (271 14
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (258 18
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (227 227 (:REWRITE |(+ c (+ d x))|))
     (226 150 (:LINEAR MOD-BOUNDS-2))
     (180 20 (:REWRITE FLOOR-POSITIVE . 2))
     (152 152 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (152 152 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (152 152 (:REWRITE MOD-NEG))
     (152 152 (:REWRITE MOD-MINUS-2))
     (152 152 (:REWRITE MOD-CANCEL-*))
     (152 152 (:REWRITE |(- (* c x))|))
     (120 120 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (120 120
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (120 120 (:LINEAR <-OF-*-AND-*))
     (112 112 (:REWRITE MOD-ZERO . 1))
     (112 112 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (82 82 (:REWRITE FOLD-CONSTS-IN-+))
     (82 82 (:REWRITE +-COMBINE-CONSTANTS))
     (80 20 (:REWRITE <-OF-0-AND-FLOOR))
     (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (40 40 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (40 40 (:REWRITE |(equal (+ c x) d)|))
     (33 33 (:REWRITE |(< (+ c x) d)|))
     (24 4 (:DEFINITION FIX))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (20 20 (:TYPE-PRESCRIPTION NATP))
     (20 20 (:REWRITE FLOOR-POSITIVE . 3))
     (20 20 (:REWRITE FLOOR-POSITIVE . 1))
     (19 19 (:REWRITE |(< d (+ c x))|))
     (18 18
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (16 16 (:REWRITE |(< (+ d x) (+ c y))|))
     (16 16 (:REWRITE |(< (+ c x) (+ d y))|))
     (16 16 (:REWRITE |(< (+ c x y) d)|))
     (14 14
         (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (14 14
         (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (11 11
         (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (11 11
         (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (10 10
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (10 10 (:REWRITE |(* c (* d x))|))
     (5 5 (:REWRITE |(< d (+ c x y))|)))
(MOD-OF-+-OF-MOD-ARG2
     (60480 192
            (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (10660 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (10460 60 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (9538 1914 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (9538 1914
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (9382 494
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8920 80 (:LINEAR FLOOR-BOUNDS-1))
     (8374 75 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (7708 7708
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (7708 7708
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (7708 7708
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7064 420 (:REWRITE MOD-ZERO . 2))
     (6886 313 (:REWRITE CANCEL-FLOOR-+))
     (6438 392 (:REWRITE DEFAULT-+-2))
     (4916 1594 (:REWRITE DEFAULT-*-2))
     (4105 1270 (:REWRITE INTEGERP-OF-*))
     (3742 494
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3640 40 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (3510 2012
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3440 420 (:REWRITE MOD-X-Y-=-X . 4))
     (3440 420 (:REWRITE MOD-X-Y-=-X . 3))
     (3344 152 (:REWRITE CANCEL-MOD-+))
     (3142 454 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3043 313 (:REWRITE FLOOR-ZERO . 4))
     (3043 313 (:REWRITE FLOOR-ZERO . 3))
     (2915 1993 (:REWRITE SIMPLIFY-SUMS-<))
     (2774 1990 (:REWRITE DEFAULT-<-2))
     (2647 75 (:LINEAR MOD-BOUNDS-3))
     (2456 174 (:REWRITE DEFAULT-UNARY-MINUS))
     (2405 2273 (:META META-INTEGERP-CORRECT))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (2392 2392
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2273 2273 (:REWRITE REDUCE-INTEGERP-+))
     (2273 2273 (:REWRITE INTEGERP-MINUS-X))
     (2232 420 (:REWRITE MOD-ZERO . 3))
     (2224 313 (:REWRITE FLOOR-WHEN-<))
     (2142 1990 (:REWRITE DEFAULT-<-1))
     (2012 2012
           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (2012 2012 (:REWRITE |(< (- x) (- y))|))
     (1986 1914
           (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (1986 1914 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (1914 1914
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1914 1914
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1914 1914
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1914 1914
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1680 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1594 1594
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1594 1594 (:REWRITE DEFAULT-*-1))
     (1565 313
           (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (1384 1384
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1384 1384 (:REWRITE DEFAULT-UNARY-/))
     (1357 1357
           (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1270 1270 (:REWRITE |(integerp (* c x))|))
     (1140 392 (:REWRITE DEFAULT-+-1))
     (1040 40 (:LINEAR FLOOR-BOUNDS-3))
     (1040 40 (:LINEAR FLOOR-BOUNDS-2))
     (1031 14
           (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (964 452
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (964 452
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (964 452
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (918 18 (:REWRITE |(* (+ x y) z)|))
     (840 840 (:REWRITE MOD-COMPLETION))
     (728 728
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (728 728 (:REWRITE |(< (- x) 0)|))
     (596 596
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (596 596 (:REWRITE |(< 0 (- x))|))
     (494 494 (:REWRITE |(equal (- x) (- y))|))
     (454 454 (:REWRITE |(equal (- x) 0)|))
     (452 452
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (440 40 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (420 420 (:REWRITE MOD-X-Y-=-X . 2))
     (414 414
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (392 392
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (320 20
          (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (313 313 (:REWRITE FLOOR-ZERO . 2))
     (313 313
          (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (313 313
          (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (313 313
          (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (313 313 (:REWRITE FLOOR-MINUS-WEAK))
     (313 313
          (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (313 313 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (313 313 (:REWRITE FLOOR-MINUS-2))
     (313 313 (:REWRITE FLOOR-COMPLETION))
     (313 313 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (280 20 (:DEFINITION NATP))
     (274 14
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (258 18
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (226 150 (:LINEAR MOD-BOUNDS-2))
     (209 209 (:REWRITE |(+ c (+ d x))|))
     (180 20 (:REWRITE FLOOR-POSITIVE . 2))
     (152 152 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (152 152 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (152 152 (:REWRITE MOD-NEG))
     (152 152 (:REWRITE MOD-MINUS-2))
     (152 152 (:REWRITE MOD-CANCEL-*))
     (152 152 (:REWRITE |(- (* c x))|))
     (120 120 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (120 120
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (120 120 (:LINEAR <-OF-*-AND-*))
     (112 112 (:REWRITE MOD-ZERO . 1))
     (112 112 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (80 20 (:REWRITE <-OF-0-AND-FLOOR))
     (76 76 (:REWRITE FOLD-CONSTS-IN-+))
     (76 76 (:REWRITE +-COMBINE-CONSTANTS))
     (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (40 40 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (40 40 (:REWRITE |(equal (+ c x) d)|))
     (33 33 (:REWRITE |(< (+ c x) d)|))
     (24 4 (:DEFINITION FIX))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (20 20 (:TYPE-PRESCRIPTION NATP))
     (20 20 (:REWRITE FLOOR-POSITIVE . 3))
     (20 20 (:REWRITE FLOOR-POSITIVE . 1))
     (19 19 (:REWRITE |(< d (+ c x))|))
     (18 18
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (16 16 (:REWRITE |(< (+ d x) (+ c y))|))
     (16 16 (:REWRITE |(< (+ c x) (+ d y))|))
     (16 16 (:REWRITE |(< (+ c x y) d)|))
     (14 14
         (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (14 14
         (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (11 11
         (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (11 11
         (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (10 10
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (10 10 (:REWRITE |(* c (* d x))|))
     (5 5 (:REWRITE |(< d (+ c x y))|)))
(EQUAL-OF-MOD-OF-+-AND-MOD-OF-+-CANCEL
     (2713 565 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2713 565
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1195 1195
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1195 1195
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1195 1195
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (740 27 (:REWRITE MOD-WHEN-MULTIPLE))
     (575 25 (:REWRITE CANCEL-MOD-+))
     (565 565
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (565 565
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (565 565
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (565 565
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (565 565
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (565 565 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (531 25 (:REWRITE MOD-ZERO . 2))
     (452 34
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (452 26 (:REWRITE DEFAULT-+-2))
     (304 76 (:REWRITE |(* y x)|))
     (300 26 (:REWRITE DEFAULT-+-1))
     (245 25 (:REWRITE MOD-X-Y-=-X . 4))
     (245 25 (:REWRITE MOD-X-Y-=-X . 3))
     (207 75 (:REWRITE INTEGERP-OF-*))
     (179 25 (:REWRITE MOD-WHEN-<))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (167 167
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (162 10 (:REWRITE DEFAULT-UNARY-MINUS))
     (157 25 (:REWRITE MOD-ZERO . 3))
     (148 72 (:REWRITE SIMPLIFY-SUMS-<))
     (148 72
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (148 72 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (148 72 (:REWRITE DEFAULT-<-1))
     (122 122 (:REWRITE REDUCE-INTEGERP-+))
     (122 122 (:REWRITE INTEGERP-MINUS-X))
     (122 122 (:META META-INTEGERP-CORRECT))
     (100 5 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (81 3 (:LINEAR MOD-BOUNDS-3))
     (76 76
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (76 76 (:REWRITE DEFAULT-*-2))
     (76 76 (:REWRITE DEFAULT-*-1))
     (75 75 (:REWRITE |(integerp (* c x))|))
     (74 74
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (74 74 (:REWRITE DEFAULT-UNARY-/))
     (72 72
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (72 72 (:REWRITE DEFAULT-<-2))
     (72 72 (:REWRITE |(< (- x) (- y))|))
     (50 50
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (50 50 (:REWRITE MOD-COMPLETION))
     (42 2 (:REWRITE |(* (+ x y) z)|))
     (39 2
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (34 34 (:REWRITE |(equal (- x) (- y))|))
     (33 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (32 32 (:REWRITE |(+ c (+ d x))|))
     (28 28
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (28 28
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (27 27
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (27 27
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (27 27
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (27 27
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (25 25
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (25 25 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (25 25 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (25 25 (:REWRITE MOD-X-Y-=-X . 2))
     (25 25 (:REWRITE MOD-NEG))
     (25 25 (:REWRITE MOD-MINUS-2))
     (25 25 (:REWRITE MOD-CANCEL-*))
     (25 25 (:REWRITE |(< (- x) 0)|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (23 23 (:REWRITE |(< 0 (- x))|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (22 22 (:REWRITE |(equal (- x) 0)|))
     (19 2
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (12 12
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (10 2
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (9 9 (:REWRITE |(equal (+ c x) d)|))
     (7 7 (:REWRITE |(equal (+ d x) (+ c y))|))
     (7 7 (:REWRITE |(equal (+ c x) (+ d y))|))
     (6 6 (:LINEAR MOD-BOUNDS-2))
     (5 5 (:REWRITE |(equal (+ c x y) d)|))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE +-COMBINE-CONSTANTS))
     (2 2
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (2 2
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE |(< (+ c x) d)|))
     (2 2 (:REWRITE |(* (- x) y)|)))
(MOD-OF-*-SUBST-ARG2
     (1367 25 (:REWRITE CANCEL-MOD-+))
     (1327 25 (:REWRITE MOD-X-Y-=-X . 3))
     (1323 25 (:REWRITE MOD-WHEN-MULTIPLE))
     (1305 301 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1305 301
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1119 25 (:REWRITE MOD-ZERO . 2))
     (942 18 (:REWRITE <-OF-*-AND-0))
     (902 46 (:REWRITE |(* (* x y) z)|))
     (865 25 (:REWRITE MOD-ZERO . 3))
     (733 25 (:REWRITE MOD-WHEN-<))
     (703 191 (:META META-INTEGERP-CORRECT))
     (659 659
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (659 659
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (659 659
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (613 25 (:REWRITE MOD-X-Y-=-X . 4))
     (538 40 (:REWRITE |(* y (* x z))|))
     (473 93 (:REWRITE INTEGERP-OF-*))
     (459 181 (:REWRITE DEFAULT-*-2))
     (416 74 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (328 14 (:REWRITE |(equal (* x y) 0)|))
     (314 65 (:REWRITE |(* y x)|))
     (301 301
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (301 301
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (301 301
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (301 301
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (299 6 (:LINEAR MOD-BOUNDS-3))
     (298 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (256 166 (:REWRITE SIMPLIFY-SUMS-<))
     (256 166
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (256 166
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (202 148 (:REWRITE DEFAULT-<-2))
     (191 191 (:REWRITE REDUCE-INTEGERP-+))
     (191 191 (:REWRITE INTEGERP-MINUS-X))
     (181 181
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (181 181 (:REWRITE DEFAULT-*-1))
     (180 180
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (180 180
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (180 180
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (180 180
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (166 166
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (166 166 (:REWRITE |(< (- x) (- y))|))
     (166 148 (:REWRITE DEFAULT-<-1))
     (160 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (148 148 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (148 148
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (148 148 (:LINEAR <-OF-*-AND-*))
     (125 125
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (125 125 (:REWRITE DEFAULT-UNARY-/))
     (124 124
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (111 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (111 39
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (111 39
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (93 93 (:REWRITE |(integerp (* c x))|))
     (86 86 (:REWRITE |(* c (* d x))|))
     (74 74 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (74 74 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (74 74 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (74 74 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (68 50 (:REWRITE MOD-COMPLETION))
     (65 65
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (65 65 (:REWRITE |(< (- x) 0)|))
     (59 59
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (59 59 (:REWRITE |(< 0 (- x))|))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (50 50
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (50 50
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (46 46 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (43 25
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (43 25
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (43 25
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (43 25 (:REWRITE MOD-NEG))
     (43 25 (:REWRITE MOD-CANCEL-*))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (39 39 (:REWRITE |(equal (- x) (- y))|))
     (38 38
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (38 38 (:REWRITE |(equal (- x) 0)|))
     (38 2 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (25 25 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (25 25 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (25 25 (:REWRITE MOD-X-Y-=-X . 2))
     (25 25
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (25 25 (:REWRITE MOD-MINUS-2))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (17 17
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (17 17
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (12 12 (:LINEAR MOD-BOUNDS-2))
     (5 1 (:REWRITE MOD-POSITIVE . 3))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-POSITIVE . 2))
     (1 1 (:REWRITE MOD-POSITIVE . 1))
     (1 1 (:REWRITE MOD-NONPOSITIVE)))
(MOD-OF-*-SUBST-ARG1
     (1206 26 (:REWRITE MOD-WHEN-MULTIPLE))
     (1159 26 (:REWRITE CANCEL-MOD-+))
     (1102 26 (:REWRITE MOD-X-Y-=-X . 3))
     (1027 279 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1027 279
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1001 26 (:REWRITE MOD-ZERO . 2))
     (820 20 (:REWRITE <-OF-*-AND-0))
     (768 52 (:REWRITE |(* (* x y) z)|))
     (646 26 (:REWRITE MOD-ZERO . 3))
     (555 102 (:REWRITE INTEGERP-OF-*))
     (524 524
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (524 524
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (524 524
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (496 26 (:REWRITE MOD-WHEN-<))
     (478 26 (:REWRITE MOD-X-Y-=-X . 4))
     (421 213 (:META META-INTEGERP-CORRECT))
     (298 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (291 6 (:LINEAR MOD-BOUNDS-3))
     (286 182 (:REWRITE DEFAULT-*-2))
     (279 279
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (279 279
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (279 279
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (279 279
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (248 26 (:REWRITE |(* y (* x z))|))
     (224 84 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (216 216
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (213 213 (:REWRITE REDUCE-INTEGERP-+))
     (213 213 (:REWRITE INTEGERP-MINUS-X))
     (208 16 (:REWRITE |(equal (* x y) 0)|))
     (186 186 (:REWRITE SIMPLIFY-SUMS-<))
     (186 186
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (186 186
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (186 186
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (186 186 (:REWRITE |(< (- x) (- y))|))
     (182 182
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (182 182 (:REWRITE DEFAULT-*-1))
     (168 168 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (168 168
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (168 168 (:LINEAR <-OF-*-AND-*))
     (166 166 (:REWRITE DEFAULT-<-2))
     (166 166 (:REWRITE DEFAULT-<-1))
     (140 140
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (136 136
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (136 136 (:REWRITE DEFAULT-UNARY-/))
     (116 44 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (116 44
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (116 44
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (102 102 (:REWRITE |(integerp (* c x))|))
     (92 92
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (92 92
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (84 84 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (84 84 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (84 84 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (84 84 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (80 80
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (78 78 (:REWRITE |(* c (* d x))|))
     (72 72
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (72 72 (:REWRITE |(< (- x) 0)|))
     (68 68
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (68 68 (:REWRITE |(< 0 (- x))|))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (52 52 (:REWRITE MOD-COMPLETION))
     (52 52 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (44 44 (:REWRITE |(equal (- x) (- y))|))
     (42 42
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (42 42 (:REWRITE |(equal (- x) 0)|))
     (38 2 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (26 26 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (26 26 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (26 26 (:REWRITE MOD-X-Y-=-X . 2))
     (26 26
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (26 26
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (26 26
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (26 26
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (26 26 (:REWRITE MOD-NEG))
     (26 26 (:REWRITE MOD-MINUS-2))
     (26 26 (:REWRITE MOD-CANCEL-*))
     (20 20 (:REWRITE |(< (* x y) 0)|))
     (16 16 (:REWRITE |(< 0 (* x y))|))
     (12 12 (:LINEAR MOD-BOUNDS-2)))
(MOD-OF-+-OF---SAME
     (462 21 (:REWRITE CANCEL-MOD-+))
     (367 83 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (367 83
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (307 21 (:REWRITE MOD-ZERO . 2))
     (198 9
          (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (172 58 (:REWRITE INTEGERP-OF-*))
     (151 21 (:REWRITE MOD-X-Y-=-X . 4))
     (151 21 (:REWRITE MOD-X-Y-=-X . 3))
     (148 4 (:LINEAR MOD-BOUNDS-3))
     (127 9 (:REWRITE |(* (+ x y) z)|))
     (112 21 (:REWRITE MOD-WHEN-<))
     (105 105 (:META META-INTEGERP-CORRECT))
     (99 21 (:REWRITE MOD-ZERO . 3))
     (96 96 (:REWRITE REDUCE-INTEGERP-+))
     (96 96 (:REWRITE INTEGERP-MINUS-X))
     (85 53 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (83 83
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (83 83 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (83 83
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (83 83 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (72 72
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (72 72 (:REWRITE DEFAULT-UNARY-/))
     (72 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (58 58
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (58 58 (:REWRITE DEFAULT-*-2))
     (58 58 (:REWRITE DEFAULT-*-1))
     (58 58 (:REWRITE |(integerp (* c x))|))
     (53 53
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (53 53
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (53 53 (:REWRITE |(< (- x) (- y))|))
     (51 51 (:REWRITE SIMPLIFY-SUMS-<))
     (51 51 (:REWRITE DEFAULT-<-2))
     (51 51 (:REWRITE DEFAULT-<-1))
     (46 10 (:REWRITE DEFAULT-+-2))
     (42 42 (:REWRITE MOD-COMPLETION))
     (40 40
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (28 28
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (24 24 (:REWRITE |(< (- x) 0)|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (21 21 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (21 21 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (21 21 (:REWRITE MOD-X-Y-=-X . 2))
     (21 21 (:REWRITE MOD-NEG))
     (21 21 (:REWRITE MOD-MINUS-2))
     (21 21 (:REWRITE MOD-CANCEL-*))
     (18 12 (:REWRITE NORMALIZE-ADDENDS))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (14 14 (:REWRITE |(< 0 (- x))|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (13 13
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (13 13 (:REWRITE |(equal (- x) 0)|))
     (13 13 (:REWRITE |(equal (- x) (- y))|))
     (12 12
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (12 12
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE DEFAULT-+-1))
     (8 8 (:LINEAR MOD-BOUNDS-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (6 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (4 4 (:REWRITE |(- (- x))|))
     (2 2 (:REWRITE |(< (+ c x) d)|))
     (2 2 (:REWRITE |(+ x (- x))|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(MOD-OF-+-OF---OF-MOD-SAME-ARG1
     (13452 198 (:REWRITE MOD-WHEN-MULTIPLE))
     (6024 1900 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (4880 286
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (4041 576 (:REWRITE INTEGERP-MINUS-X))
     (2988 2988
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2988 2988
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2988 2988
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2595 7 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (2461 169 (:REWRITE DEFAULT-+-2))
     (1972 1900
           (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (1972 1900 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (1900 1900
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1900 1900
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1900 1900
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1794 14
           (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (1760 112 (:REWRITE CANCEL-MOD-+))
     (1564 112 (:REWRITE MOD-ZERO . 2))
     (1495 58 (:REWRITE |(* (- x) y)|))
     (1373 373
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1321 366 (:REWRITE DEFAULT-*-2))
     (1215 65 (:REWRITE |(* y x)|))
     (1172 112 (:REWRITE MOD-X-Y-=-X . 4))
     (1172 112 (:REWRITE MOD-X-Y-=-X . 3))
     (1103 115 (:REWRITE DEFAULT-UNARY-MINUS))
     (1099 7 (:LINEAR MOD-BOUNDS-3))
     (1039 1039
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (921 318 (:REWRITE INTEGERP-OF-*))
     (894 14 (:REWRITE |(* (+ x y) z)|))
     (816 165
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (816 165
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (816 165
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (576 576 (:META META-INTEGERP-CORRECT))
     (557 348 (:REWRITE DEFAULT-<-1))
     (533 533 (:REWRITE REDUCE-INTEGERP-+))
     (522 169 (:REWRITE DEFAULT-+-1))
     (508 112 (:REWRITE MOD-ZERO . 3))
     (485 348 (:REWRITE DEFAULT-<-2))
     (384 384
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (373 373 (:REWRITE |(< (- x) (- y))|))
     (366 366
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (366 366 (:REWRITE DEFAULT-*-1))
     (366 14
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (352 352
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (352 352 (:REWRITE DEFAULT-UNARY-/))
     (318 318 (:REWRITE |(integerp (* c x))|))
     (286 286
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (286 286
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (286 286
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (278 278
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (224 224 (:REWRITE MOD-COMPLETION))
     (169 169
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (165 165
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (144 144 (:REWRITE |(+ c (+ d x))|))
     (124 124 (:REWRITE |(< (- x) 0)|))
     (121 121
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (112 112 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (112 112 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (112 112 (:REWRITE MOD-X-Y-=-X . 2))
     (112 112 (:REWRITE MOD-NEG))
     (112 112 (:REWRITE MOD-MINUS-2))
     (112 112 (:REWRITE MOD-CANCEL-*))
     (107 107
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (107 107 (:REWRITE |(< 0 (- x))|))
     (90 14 (:LINEAR MOD-BOUNDS-2))
     (88 88
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (88 88 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (88 88
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (88 88
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (88 88 (:REWRITE |(equal (- x) 0)|))
     (88 88 (:REWRITE |(equal (- x) (- y))|))
     (70 14
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (47 47 (:REWRITE |(- (* c x))|))
     (32 32 (:REWRITE FOLD-CONSTS-IN-+))
     (32 32 (:REWRITE +-COMBINE-CONSTANTS))
     (25 25 (:REWRITE |(< (+ c x) d)|))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (22 22 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (14 14
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (11 11 (:REWRITE |(< d (+ c x))|))
     (11 11 (:REWRITE |(< (+ d x) (+ c y))|))
     (11 11 (:REWRITE |(< (+ c x) (+ d y))|))
     (11 11 (:REWRITE |(< (+ c x y) d)|))
     (10 10
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD)))
(MOD-OF-+-OF---OF-MOD-SAME-ARG2
     (13449 198 (:REWRITE MOD-WHEN-MULTIPLE))
     (6024 1900 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (4880 286
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (4041 576 (:REWRITE INTEGERP-MINUS-X))
     (2988 2988
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2988 2988
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2988 2988
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2603 7 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (2452 160 (:REWRITE DEFAULT-+-2))
     (1972 1900
           (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (1972 1900 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (1900 1900
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1900 1900
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1900 1900
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1794 14
           (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (1760 112 (:REWRITE CANCEL-MOD-+))
     (1564 112 (:REWRITE MOD-ZERO . 2))
     (1495 58 (:REWRITE |(* (- x) y)|))
     (1373 373
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1321 366 (:REWRITE DEFAULT-*-2))
     (1215 65 (:REWRITE |(* y x)|))
     (1172 112 (:REWRITE MOD-X-Y-=-X . 4))
     (1172 112 (:REWRITE MOD-X-Y-=-X . 3))
     (1103 115 (:REWRITE DEFAULT-UNARY-MINUS))
     (1098 7 (:LINEAR MOD-BOUNDS-3))
     (1039 1039
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (921 318 (:REWRITE INTEGERP-OF-*))
     (890 14 (:REWRITE |(* (+ x y) z)|))
     (816 165
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (816 165
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (816 165
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (576 576 (:META META-INTEGERP-CORRECT))
     (557 348 (:REWRITE DEFAULT-<-1))
     (533 533 (:REWRITE REDUCE-INTEGERP-+))
     (513 160 (:REWRITE DEFAULT-+-1))
     (508 112 (:REWRITE MOD-ZERO . 3))
     (485 348 (:REWRITE DEFAULT-<-2))
     (384 384
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (373 373 (:REWRITE |(< (- x) (- y))|))
     (366 366
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (366 366 (:REWRITE DEFAULT-*-1))
     (366 14
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (352 352
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (352 352 (:REWRITE DEFAULT-UNARY-/))
     (318 318 (:REWRITE |(integerp (* c x))|))
     (286 286
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (286 286
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (286 286
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (278 278
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (224 224 (:REWRITE MOD-COMPLETION))
     (165 165
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (160 160
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (126 126 (:REWRITE |(+ c (+ d x))|))
     (124 124 (:REWRITE |(< (- x) 0)|))
     (121 121
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (112 112 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (112 112 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (112 112 (:REWRITE MOD-X-Y-=-X . 2))
     (112 112 (:REWRITE MOD-NEG))
     (112 112 (:REWRITE MOD-MINUS-2))
     (112 112 (:REWRITE MOD-CANCEL-*))
     (107 107
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (107 107 (:REWRITE |(< 0 (- x))|))
     (90 14 (:LINEAR MOD-BOUNDS-2))
     (88 88
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (88 88 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (88 88
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (88 88
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (88 88 (:REWRITE |(equal (- x) 0)|))
     (88 88 (:REWRITE |(equal (- x) (- y))|))
     (70 14
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (47 47 (:REWRITE |(- (* c x))|))
     (25 25 (:REWRITE |(< (+ c x) d)|))
     (23 23 (:REWRITE FOLD-CONSTS-IN-+))
     (23 23 (:REWRITE +-COMBINE-CONSTANTS))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (22 22
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (22 22 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (14 14
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (11 11 (:REWRITE |(< d (+ c x))|))
     (11 11 (:REWRITE |(< (+ d x) (+ c y))|))
     (11 11 (:REWRITE |(< (+ c x) (+ d y))|))
     (11 11 (:REWRITE |(< (+ c x y) d)|))
     (10 10
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (7 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (5 1 (:REWRITE BUBBLE-DOWN-+-BUBBLE-DOWN)))
(MOD-OF-+-SAME-ARG1
     (462 21 (:REWRITE CANCEL-MOD-+))
     (367 83 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (367 83
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (307 21 (:REWRITE MOD-ZERO . 2))
     (198 9
          (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (172 58 (:REWRITE INTEGERP-OF-*))
     (151 21 (:REWRITE MOD-X-Y-=-X . 4))
     (151 21 (:REWRITE MOD-X-Y-=-X . 3))
     (146 4 (:LINEAR MOD-BOUNDS-3))
     (118 9 (:REWRITE |(* (+ x y) z)|))
     (112 21 (:REWRITE MOD-WHEN-<))
     (105 105 (:META META-INTEGERP-CORRECT))
     (99 21 (:REWRITE MOD-ZERO . 3))
     (96 96 (:REWRITE REDUCE-INTEGERP-+))
     (96 96 (:REWRITE INTEGERP-MINUS-X))
     (83 83
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (83 83 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (83 83
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (83 83 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (72 72
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (72 72 (:REWRITE DEFAULT-UNARY-/))
     (58 58
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (58 58 (:REWRITE DEFAULT-*-2))
     (58 58 (:REWRITE DEFAULT-*-1))
     (58 58 (:REWRITE |(integerp (* c x))|))
     (51 51 (:REWRITE SIMPLIFY-SUMS-<))
     (51 51
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (51 51
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (51 51 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (51 51 (:REWRITE DEFAULT-<-2))
     (51 51 (:REWRITE DEFAULT-<-1))
     (51 51 (:REWRITE |(< (- x) (- y))|))
     (50 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (46 10 (:REWRITE DEFAULT-+-2))
     (42 42 (:REWRITE MOD-COMPLETION))
     (38 38
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (28 28
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (24 24 (:REWRITE |(< (- x) 0)|))
     (21 21 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (21 21 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (21 21 (:REWRITE MOD-X-Y-=-X . 2))
     (21 21 (:REWRITE MOD-NEG))
     (21 21 (:REWRITE MOD-MINUS-2))
     (21 21 (:REWRITE MOD-CANCEL-*))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (14 14 (:REWRITE |(< 0 (- x))|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (13 13
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (13 13 (:REWRITE |(equal (- x) 0)|))
     (13 13 (:REWRITE |(equal (- x) (- y))|))
     (12 12
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (12 12
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-+-1))
     (8 8 (:LINEAR MOD-BOUNDS-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (2 2
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE |(< (+ c x) d)|)))
(MOD-OF-+-SAME-ARG2
     (462 21 (:REWRITE CANCEL-MOD-+))
     (367 83 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (367 83
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (307 21 (:REWRITE MOD-ZERO . 2))
     (198 9
          (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (172 58 (:REWRITE INTEGERP-OF-*))
     (151 21 (:REWRITE MOD-X-Y-=-X . 4))
     (151 21 (:REWRITE MOD-X-Y-=-X . 3))
     (148 4 (:LINEAR MOD-BOUNDS-3))
     (126 9 (:REWRITE |(* (+ x y) z)|))
     (112 21 (:REWRITE MOD-WHEN-<))
     (106 106 (:META META-INTEGERP-CORRECT))
     (99 21 (:REWRITE MOD-ZERO . 3))
     (97 97 (:REWRITE REDUCE-INTEGERP-+))
     (97 97 (:REWRITE INTEGERP-MINUS-X))
     (83 83
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (83 83 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (83 83
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (83 83
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (83 83 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (72 72
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (72 72 (:REWRITE DEFAULT-UNARY-/))
     (58 58
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (58 58 (:REWRITE DEFAULT-*-2))
     (58 58 (:REWRITE DEFAULT-*-1))
     (58 58 (:REWRITE |(integerp (* c x))|))
     (51 51 (:REWRITE SIMPLIFY-SUMS-<))
     (51 51
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (51 51
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (51 51 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (51 51 (:REWRITE DEFAULT-<-2))
     (51 51 (:REWRITE DEFAULT-<-1))
     (51 51 (:REWRITE |(< (- x) (- y))|))
     (50 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (46 10 (:REWRITE DEFAULT-+-2))
     (42 42 (:REWRITE MOD-COMPLETION))
     (38 38
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (28 28
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (24 24 (:REWRITE |(< (- x) 0)|))
     (21 21 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (21 21 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (21 21 (:REWRITE MOD-X-Y-=-X . 2))
     (21 21 (:REWRITE MOD-NEG))
     (21 21 (:REWRITE MOD-MINUS-2))
     (21 21 (:REWRITE MOD-CANCEL-*))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (14 14 (:REWRITE |(< 0 (- x))|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (13 13
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (13 13 (:REWRITE |(equal (- x) 0)|))
     (13 13 (:REWRITE |(equal (- x) (- y))|))
     (12 12
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (12 12
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-+-1))
     (8 8 (:LINEAR MOD-BOUNDS-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (2 2
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE |(< (+ c x) d)|)))
(MULTIPLE-WHEN-MOD-0-CHEAP
     (20 2 (:LINEAR MOD-BOUNDS-2))
     (20 2 (:LINEAR MOD-BOUNDS-1))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (17 1 (:REWRITE MOD-WHEN-MULTIPLE))
     (15 15
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (15 15
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (15 15
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (15 15
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (15 15 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (15 15 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (15 15
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (15 15
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (15 15
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (11 1 (:REWRITE MOD-X-Y-=-X . 4))
     (11 1 (:REWRITE MOD-X-Y-=-X . 3))
     (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10 (:REWRITE |(equal (- x) 0)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (10 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (8 2 (:REWRITE DEFAULT-UNARY-/))
     (8 1 (:REWRITE MOD-WHEN-<))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (7 1 (:REWRITE MOD-ZERO . 3))
     (7 1 (:REWRITE MOD-ZERO . 2))
     (7 1 (:REWRITE CANCEL-MOD-+))
     (7 1 (:LINEAR MOD-BOUNDS-3))
     (5 5 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (4 4 (:REWRITE |(< 0 (- x))|))
     (4 4 (:REWRITE |(< (- x) 0)|))
     (3 3
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK)))
(EQUAL-OF-0-AND-MOD-OF-1
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (20 20
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (20 20
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (20 20
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (20 20
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (20 20
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (11 1 (:REWRITE MOD-X-Y-=-X . 4))
     (11 1 (:REWRITE MOD-X-Y-=-X . 3))
     (8 1 (:REWRITE MOD-WHEN-<))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (7 1 (:REWRITE MOD-ZERO . 3))
     (6 1 (:REWRITE MOD-ZERO . 2))
     (6 1 (:REWRITE MOD-WHEN-MULTIPLE))
     (6 1 (:REWRITE CANCEL-MOD-+))
     (4 1 (:REWRITE MOD-X-1))
     (4 1 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE |(equal (- x) 0)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) 0)|)))
(MOD-BOUND-LINEAR-ARG2-STRONG
     (192 40 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (192 40
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (40 40 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (40 40
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (40 40 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (40 40
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (40 40
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (26 1 (:REWRITE MOD-WHEN-MULTIPLE))
     (23 1 (:REWRITE MOD-ZERO . 2))
     (22 1 (:REWRITE CANCEL-MOD-+))
     (17 17
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (11 1 (:REWRITE MOD-X-Y-=-X . 4))
     (11 1 (:REWRITE MOD-X-Y-=-X . 3))
     (9 3 (:REWRITE INTEGERP-OF-*))
     (8 1 (:REWRITE MOD-WHEN-<))
     (7 1 (:REWRITE MOD-ZERO . 3))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE DEFAULT-UNARY-/))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE DEFAULT-*-2))
     (3 3 (:REWRITE DEFAULT-*-1))
     (3 3 (:REWRITE |(integerp (* c x))|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (2 2
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (2 2 (:REWRITE MOD-COMPLETION))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE |(equal (- x) 0)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) 0)|)))
(<-OF-MOD-SAME2 (115 23 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (115 23
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (26 1 (:REWRITE MOD-WHEN-MULTIPLE))
                (23 23 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (23 23
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (23 23 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (23 23
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (23 23
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (23 23
                    (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                (23 23 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                (23 1 (:REWRITE MOD-ZERO . 2))
                (22 1 (:REWRITE CANCEL-MOD-+))
                (11 1 (:REWRITE MOD-X-Y-=-X . 4))
                (11 1 (:REWRITE MOD-X-Y-=-X . 3))
                (9 3 (:REWRITE INTEGERP-OF-*))
                (8 1 (:REWRITE MOD-WHEN-<))
                (7 1 (:REWRITE MOD-ZERO . 3))
                (6 6 (:REWRITE REDUCE-INTEGERP-+))
                (6 6 (:REWRITE INTEGERP-MINUS-X))
                (6 6 (:META META-INTEGERP-CORRECT))
                (4 1
                   (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
                (3 3 (:REWRITE SIMPLIFY-SUMS-<))
                (3 3
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (3 3
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (3 3
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (3 3
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (3 3 (:REWRITE DEFAULT-UNARY-/))
                (3 3 (:REWRITE DEFAULT-<-2))
                (3 3 (:REWRITE DEFAULT-<-1))
                (3 3 (:REWRITE DEFAULT-*-2))
                (3 3 (:REWRITE DEFAULT-*-1))
                (3 3 (:REWRITE |(integerp (* c x))|))
                (3 3 (:REWRITE |(< (- x) (- y))|))
                (2 2
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (2 2 (:REWRITE MOD-COMPLETION))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (1 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (1 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
                (1 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
                (1 1
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (1 1 (:REWRITE MOD-X-Y-=-X . 2))
                (1 1
                   (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
                (1 1
                   (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
                (1 1
                   (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
                (1 1
                   (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
                (1 1 (:REWRITE MOD-NEG))
                (1 1 (:REWRITE MOD-MINUS-2))
                (1 1 (:REWRITE MOD-CANCEL-*))
                (1 1 (:REWRITE |(equal (- x) 0)|))
                (1 1 (:REWRITE |(equal (- x) (- y))|))
                (1 1 (:REWRITE |(< 0 (- x))|))
                (1 1 (:REWRITE |(< (- x) 0)|)))
(EQUAL-OF-MOD-SAME
     (236 128 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (159 159
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (159 159
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (159 159
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (159 159
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (148 5 (:REWRITE MOD-WHEN-MULTIPLE))
     (128 128
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (128 128
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (128 128 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (128 128
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (128 128
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (128 128
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (128 128
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (128 128
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (128 128
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (128 128
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (128 128 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (106 33 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (106 33
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (106 33
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (80 8 (:LINEAR MOD-BOUNDS-2))
     (80 8 (:LINEAR MOD-BOUNDS-1))
     (67 5 (:REWRITE MOD-ZERO . 2))
     (66 4 (:LINEAR MOD-BOUNDS-3))
     (65 5 (:REWRITE CANCEL-MOD-+))
     (55 5 (:REWRITE MOD-X-Y-=-X . 4))
     (55 5 (:REWRITE MOD-X-Y-=-X . 3))
     (44 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (41 41 (:REWRITE SIMPLIFY-SUMS-<))
     (41 41
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (41 41
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (41 41 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (41 41 (:REWRITE DEFAULT-<-2))
     (41 41 (:REWRITE DEFAULT-<-1))
     (41 41 (:REWRITE |(< (- x) (- y))|))
     (40 5 (:REWRITE MOD-WHEN-<))
     (40 4 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (38 11 (:REWRITE INTEGERP-OF-*))
     (33 33 (:REWRITE |(equal (- x) (- y))|))
     (31 13 (:REWRITE DEFAULT-UNARY-/))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (28 28 (:REWRITE |(equal (- x) 0)|))
     (26 26 (:REWRITE REDUCE-INTEGERP-+))
     (26 26 (:REWRITE INTEGERP-MINUS-X))
     (26 26 (:META META-INTEGERP-CORRECT))
     (23 5 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (23 5 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (23 5 (:REWRITE MOD-ZERO . 3))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (17 17 (:REWRITE |(< 0 (- x))|))
     (17 17 (:REWRITE |(< (- x) 0)|))
     (16 4
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (16 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (15 15
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (15 15 (:REWRITE DEFAULT-*-2))
     (15 15 (:REWRITE DEFAULT-*-1))
     (14 14
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (11 11 (:REWRITE |(integerp (* c x))|))
     (10 10
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (10 10 (:REWRITE MOD-COMPLETION))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE MOD-X-Y-=-X . 2))
     (5 5
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (5 5 (:REWRITE MOD-NEG))
     (5 5 (:REWRITE MOD-MINUS-2))
     (5 5 (:REWRITE MOD-CANCEL-*))
     (5 5 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (4 4
        (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (4 4 (:LINEAR <-OF-*-AND-*))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1)))
(EQUAL-OF-+-1-AND-*-2-OF-FLOOR-OF-2
     (1286 11
           (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (622 126 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (622 126
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (570 30 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (498 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (407 11 (:REWRITE CANCEL-FLOOR-+))
     (289 51 (:REWRITE DEFAULT-*-2))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (222 6 (:REWRITE CANCEL-MOD-+))
     (219 2 (:LINEAR FLOOR-BOUNDS-1))
     (210 10 (:REWRITE MOD-ZERO . 2))
     (210 10 (:REWRITE MOD-WHEN-MULTIPLE))
     (156 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (126 126
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (126 126
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (126 126
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (126 126
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (126 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (125 9 (:REWRITE DEFAULT-+-2))
     (105 1 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (105 1 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
     (101 11 (:REWRITE FLOOR-ZERO . 4))
     (101 11 (:REWRITE FLOOR-ZERO . 3))
     (88 88 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (88 88 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (88 88 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (88 88
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (74 11 (:REWRITE FLOOR-WHEN-<))
     (60 10 (:REWRITE MOD-X-Y-=-X . 4))
     (60 10 (:REWRITE MOD-X-Y-=-X . 3))
     (55 11
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (51 51
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (51 51 (:REWRITE DEFAULT-*-1))
     (50 10 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
     (45 10 (:REWRITE MOD-WHEN-<))
     (44 44 (:REWRITE SIMPLIFY-SUMS-<))
     (44 44
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (44 44
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (44 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (44 44 (:REWRITE DEFAULT-<-2))
     (44 44 (:REWRITE DEFAULT-<-1))
     (44 44 (:REWRITE |(< (- x) (- y))|))
     (41 1 (:LINEAR MOD-BOUNDS-3))
     (41 1 (:LINEAR FLOOR-BOUNDS-3))
     (41 1 (:LINEAR FLOOR-BOUNDS-2))
     (40 10 (:REWRITE MOD-ZERO . 3))
     (31 31 (:REWRITE REDUCE-INTEGERP-+))
     (31 31 (:REWRITE INTEGERP-MINUS-X))
     (31 31 (:META META-INTEGERP-CORRECT))
     (30 30
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (30 30 (:REWRITE INTEGERP-OF-*))
     (30 30 (:REWRITE |(integerp (* c x))|))
     (20 20 (:REWRITE MOD-COMPLETION))
     (18 4 (:REWRITE |(equal (+ c x) d)|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (16 16 (:REWRITE |(< (- x) 0)|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:REWRITE |(< 0 (- x))|))
     (11 11 (:REWRITE FLOOR-ZERO . 2))
     (11 11
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (11 11
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (11 11
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (11 11 (:REWRITE FLOOR-MINUS-WEAK))
     (11 11
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (11 11 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (11 11 (:REWRITE FLOOR-MINUS-2))
     (11 11 (:REWRITE FLOOR-COMPLETION))
     (11 11 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (11 1 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (10 10 (:REWRITE MOD-X-Y-=-X . 2))
     (10 10
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (10 10
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (10 10
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (10 10
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (10 10 (:REWRITE |(equal (- x) 0)|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE DEFAULT-+-1))
     (6 6 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (6 6 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (6 6 (:REWRITE MOD-NEG))
     (6 6 (:REWRITE MOD-MINUS-2))
     (6 6 (:REWRITE MOD-CANCEL-*))
     (6 6 (:REWRITE *-OF---ARG1))
     (6 6 (:REWRITE |(* (- x) y)|))
     (4 4 (:REWRITE MOD-ZERO . 1))
     (4 4 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (2 2
        (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (2 2
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:LINEAR MOD-BOUNDS-2))
     (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT)))
(*-OF-2-AND-FLOOR-OF-2
     (864 180 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (864 180
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (798 6 (:LINEAR MOD-BOUNDS-1))
     (434 12 (:REWRITE MOD-ZERO . 2))
     (426 12 (:REWRITE CANCEL-MOD-+))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (404 404
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (399 3 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (326 1
          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (200 4 (:LINEAR FLOOR-BOUNDS-2))
     (197 3 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (197 3 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
     (187 187
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (187 187
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (187 187
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (187 187
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (180 180 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (180 180
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (180 180
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (180 180
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (180 180
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (122 12 (:REWRITE MOD-X-Y-=-X . 4))
     (122 12 (:REWRITE MOD-X-Y-=-X . 3))
     (110 4 (:LINEAR FLOOR-BOUNDS-3))
     (110 3 (:LINEAR MOD-BOUNDS-3))
     (109 95 (:REWRITE DEFAULT-*-2))
     (95 95
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (95 95 (:REWRITE DEFAULT-*-1))
     (89 12 (:REWRITE MOD-WHEN-<))
     (80 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (78 12 (:REWRITE MOD-ZERO . 3))
     (68 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (68 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (68 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (68 68
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (66 6 (:REWRITE FLOOR-ZERO . 4))
     (66 6 (:REWRITE FLOOR-ZERO . 3))
     (65 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (60 12 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
     (57 57 (:REWRITE SIMPLIFY-SUMS-<))
     (57 57
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (57 57
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (57 57 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (57 57 (:REWRITE DEFAULT-<-2))
     (57 57 (:REWRITE DEFAULT-<-1))
     (57 57 (:REWRITE |(< (- x) (- y))|))
     (49 49 (:REWRITE REDUCE-INTEGERP-+))
     (49 49 (:REWRITE INTEGERP-MINUS-X))
     (49 49 (:META META-INTEGERP-CORRECT))
     (48 6 (:REWRITE FLOOR-WHEN-<))
     (47 47 (:REWRITE INTEGERP-OF-*))
     (47 47 (:REWRITE |(integerp (* c x))|))
     (40 40
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (33 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (33 3 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (31 5 (:REWRITE DEFAULT-+-2))
     (30 6
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (24 24 (:REWRITE MOD-COMPLETION))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (23 23 (:REWRITE |(< (- x) 0)|))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (17 17 (:REWRITE |(< 0 (- x))|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (13 13 (:REWRITE |(equal (- x) 0)|))
     (12 12 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (12 12 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (12 12 (:REWRITE MOD-X-Y-=-X . 2))
     (12 12
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (12 12
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (12 12
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (12 12
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (12 12 (:REWRITE MOD-NEG))
     (12 12 (:REWRITE MOD-MINUS-2))
     (12 12 (:REWRITE MOD-CANCEL-*))
     (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (9 9 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (9 9
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (9 9
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (9 9
        (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (6 6 (:REWRITE FLOOR-ZERO . 2))
     (6 6
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (6 6
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (6 6
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (6 6 (:REWRITE FLOOR-MINUS-WEAK))
     (6 6
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (6 6 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (6 6 (:REWRITE FLOOR-MINUS-2))
     (6 6 (:REWRITE FLOOR-COMPLETION))
     (6 6 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (6 6 (:LINEAR MOD-BOUNDS-2))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (1 1 (:REWRITE |(equal (+ c x) d)|)))
(SPLIT-LOW-BIT (2970 11
                     (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
               (1180 59 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
               (989 15
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (874 23 (:REWRITE CANCEL-FLOOR-+))
               (672 136 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
               (672 136
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
               (424 4 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
               (358 92 (:REWRITE DEFAULT-*-2))
               (327 327
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
               (327 327
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (327 327
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (327 327
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (304 8 (:REWRITE CANCEL-MOD-+))
               (301 14 (:REWRITE MOD-ZERO . 2))
               (301 14 (:REWRITE MOD-WHEN-MULTIPLE))
               (252 6 (:LINEAR FLOOR-BOUNDS-3))
               (252 6 (:LINEAR FLOOR-BOUNDS-2))
               (233 23 (:REWRITE FLOOR-ZERO . 4))
               (233 23 (:REWRITE FLOOR-ZERO . 3))
               (170 23 (:REWRITE FLOOR-WHEN-<))
               (157 15
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (150 150
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
               (150 150
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (150 150
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (150 150
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (142 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (140 12 (:REWRITE DEFAULT-+-2))
               (136 136 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
               (136 136
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
               (136 136
                    (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
               (136 136
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
               (136 136
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
               (136 136
                    (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
               (136 136 (:TYPE-PRESCRIPTION INTEGERP-MOD))
               (115 23
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
               (92 92
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (92 92 (:REWRITE DEFAULT-*-1))
               (90 90 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
               (90 90 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
               (90 90 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
               (90 90
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
               (90 90 (:REWRITE SIMPLIFY-SUMS-<))
               (90 90
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
               (90 90
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
               (90 90 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
               (90 90 (:REWRITE DEFAULT-<-2))
               (90 90 (:REWRITE DEFAULT-<-1))
               (90 90 (:REWRITE |(< (- x) (- y))|))
               (84 14 (:REWRITE MOD-X-Y-=-X . 4))
               (84 14 (:REWRITE MOD-X-Y-=-X . 3))
               (84 2 (:LINEAR MOD-BOUNDS-3))
               (70 14 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
               (65 65 (:REWRITE REDUCE-INTEGERP-+))
               (65 65 (:REWRITE INTEGERP-MINUS-X))
               (65 65 (:META META-INTEGERP-CORRECT))
               (63 14 (:REWRITE MOD-WHEN-<))
               (62 62
                   (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
               (59 59 (:REWRITE INTEGERP-OF-*))
               (59 59 (:REWRITE |(integerp (* c x))|))
               (56 14 (:REWRITE MOD-ZERO . 3))
               (44 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
               (34 34
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
               (34 34 (:REWRITE |(< (- x) 0)|))
               (28 28
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
               (28 28 (:REWRITE MOD-COMPLETION))
               (28 28 (:REWRITE |(< 0 (- x))|))
               (23 23 (:REWRITE FLOOR-ZERO . 2))
               (23 23
                   (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
               (23 23
                   (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
               (23 23
                   (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
               (23 23 (:REWRITE FLOOR-MINUS-WEAK))
               (23 23
                   (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
               (23 23 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
               (23 23 (:REWRITE FLOOR-MINUS-2))
               (23 23 (:REWRITE FLOOR-COMPLETION))
               (23 23 (:REWRITE FLOOR-CANCEL-*-WEAK))
               (22 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
               (16 4 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
               (15 15 (:REWRITE |(equal (- x) (- y))|))
               (14 14 (:REWRITE MOD-X-Y-=-X . 2))
               (14 14
                   (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
               (14 14
                   (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
               (14 14
                   (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
               (14 14
                   (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
               (14 14 (:REWRITE |(equal (- x) 0)|))
               (13 13
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
               (12 12
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (12 12 (:REWRITE DEFAULT-+-1))
               (8 8 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
               (8 8 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
               (8 8 (:REWRITE MOD-NEG))
               (8 8 (:REWRITE MOD-MINUS-2))
               (8 8 (:REWRITE MOD-CANCEL-*))
               (8 8 (:REWRITE *-OF---ARG1))
               (8 8 (:REWRITE |(* (- x) y)|))
               (8 2
                  (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
               (6 6 (:REWRITE MOD-ZERO . 1))
               (6 6 (:REWRITE MOD-+-CANCEL-0-WEAK))
               (4 4 (:LINEAR MOD-BOUNDS-2))
               (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
               (2 2
                  (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
               (2 2
                  (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
               (2 2 (:REWRITE |(+ c (+ d x))|))
               (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
               (1 1 (:REWRITE |(equal (+ c x) d)|)))
(FLOOR-OF-2-CASES
     (827 827
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (827 827
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (827 827
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (798 42 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (753 161 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (753 161
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (407 11 (:REWRITE CANCEL-MOD-+))
     (384 2 (:LINEAR MOD-BOUNDS-1))
     (371 11 (:REWRITE MOD-ZERO . 2))
     (371 11 (:REWRITE MOD-WHEN-MULTIPLE))
     (326 1
          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (275 25 (:REWRITE FLOOR-ZERO . 4))
     (275 25 (:REWRITE FLOOR-ZERO . 3))
     (221 25 (:REWRITE CANCEL-FLOOR-+))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (200 25 (:REWRITE FLOOR-WHEN-<))
     (192 1
          (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (192 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (169 155 (:REWRITE DEFAULT-*-2))
     (161 161 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (161 161
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (161 161
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (161 161
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (161 161
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (155 155
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (155 155 (:REWRITE DEFAULT-*-1))
     (147 147 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (147 147 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (147 147 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (147 147
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (125 25
          (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (123 123
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (122 122 (:REWRITE |(< (- x) (- y))|))
     (111 23
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (110 110 (:REWRITE DEFAULT-<-2))
     (110 110 (:REWRITE DEFAULT-<-1))
     (101 11 (:REWRITE MOD-X-Y-=-X . 4))
     (101 11 (:REWRITE MOD-X-Y-=-X . 3))
     (96 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (93 43 (:REWRITE DEFAULT-+-2))
     (89 89
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (74 11 (:REWRITE MOD-WHEN-<))
     (65 11 (:REWRITE MOD-ZERO . 3))
     (55 11 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
     (48 48 (:REWRITE REDUCE-INTEGERP-+))
     (48 48 (:REWRITE INTEGERP-MINUS-X))
     (48 48 (:META META-INTEGERP-CORRECT))
     (47 5 (:REWRITE |(equal (+ c x) d)|))
     (44 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (43 43
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (43 43 (:REWRITE DEFAULT-+-1))
     (42 42 (:REWRITE INTEGERP-OF-*))
     (42 42 (:REWRITE |(integerp (* c x))|))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (41 1 (:LINEAR MOD-BOUNDS-3))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (40 40 (:REWRITE |(< (- x) 0)|))
     (40 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (36 36 (:REWRITE |(< 0 (- x))|))
     (36 4 (:LINEAR FLOOR-BOUNDS-2))
     (25 25 (:REWRITE FLOOR-ZERO . 2))
     (25 25
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (25 25
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (25 25
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (25 25 (:REWRITE FLOOR-MINUS-WEAK))
     (25 25
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (25 25 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (25 25 (:REWRITE FLOOR-MINUS-2))
     (25 25 (:REWRITE FLOOR-COMPLETION))
     (25 25 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (23 23 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:REWRITE MOD-COMPLETION))
     (19 19
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (18 18 (:REWRITE |(equal (- x) 0)|))
     (13 13
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (13 13
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (13 13
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (11 11 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (11 11 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (11 11 (:REWRITE MOD-X-Y-=-X . 2))
     (11 11
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (11 11
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (11 11
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (11 11
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (11 11 (:REWRITE MOD-NEG))
     (11 11 (:REWRITE MOD-MINUS-2))
     (11 11 (:REWRITE MOD-CANCEL-*))
     (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (10 6 (:REWRITE |(< d (+ c x))|))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 8 (:REWRITE DEFAULT-UNARY-/))
     (8 4 (:REWRITE |(< (+ c x) d)|))
     (6 6 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (6 6 (:REWRITE *-OF---ARG1))
     (6 6 (:REWRITE |(* (- x) y)|))
     (6 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (6 6
        (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (6 6 (:LINEAR <-OF-*-AND-*))
     (4 4
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (4 4
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (3 3 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (3 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (2 2 (:LINEAR MOD-BOUNDS-2)))
(EQUAL-OF-*-2-OF-FLOOR-OF-2-SAME
     (1294 10
           (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (207 25 (:REWRITE DEFAULT-*-2))
     (144 9 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (136 4 (:REWRITE CANCEL-FLOOR-+))
     (102 3 (:REWRITE CANCEL-MOD-+))
     (78 4 (:REWRITE MOD-WHEN-MULTIPLE))
     (67 67 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (67 67 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (67 67 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (67 67
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (64 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (62 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (52 4
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (46 4 (:REWRITE DEFAULT-+-2))
     (36 36
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (36 36 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (36 36
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (36 36
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (36 36 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (36 36 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (36 36
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (36 36
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (36 36 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (36 36 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (36 36
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (36 36
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (36 36
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (36 36 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (32 8 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (25 25
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (25 25 (:REWRITE DEFAULT-*-1))
     (25 4 (:REWRITE FLOOR-WHEN-<))
     (20 4 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
     (19 19 (:REWRITE REDUCE-INTEGERP-+))
     (19 19 (:REWRITE INTEGERP-MINUS-X))
     (19 19 (:META META-INTEGERP-CORRECT))
     (18 4 (:REWRITE MOD-WHEN-<))
     (16 16 (:LINEAR FLOOR-BOUNDS-1))
     (9 9 (:REWRITE INTEGERP-OF-*))
     (9 9 (:REWRITE |(integerp (* c x))|))
     (8 8 (:REWRITE MOD-COMPLETION))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (8 8 (:LINEAR FLOOR-BOUNDS-3))
     (8 8 (:LINEAR FLOOR-BOUNDS-2))
     (8 8 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (8 2
        (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 4 (:REWRITE FLOOR-COMPLETION))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE MOD-ZERO . 3))
     (4 4 (:REWRITE MOD-ZERO . 2))
     (4 4 (:REWRITE MOD-X-Y-=-X . 4))
     (4 4 (:REWRITE MOD-X-Y-=-X . 3))
     (4 4 (:REWRITE MOD-X-Y-=-X . 2))
     (4 4
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (4 4
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (4 4
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (4 4
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (4 4 (:REWRITE FLOOR-ZERO . 4))
     (4 4 (:REWRITE FLOOR-ZERO . 3))
     (4 4 (:REWRITE FLOOR-ZERO . 2))
     (4 4
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (4 4
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (4 4
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (4 4 (:REWRITE FLOOR-MINUS-WEAK))
     (4 4
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (4 4 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (4 4 (:REWRITE FLOOR-MINUS-2))
     (4 4 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (4 4 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE |(equal (- x) 0)|))
     (4 4 (:REWRITE |(equal (+ c x) d)|))
     (4 4 (:LINEAR MOD-BOUNDS-2))
     (4 4 (:LINEAR MOD-BOUNDS-1))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (3 3 (:REWRITE MOD-NEG))
     (3 3 (:REWRITE MOD-MINUS-2))
     (3 3 (:REWRITE MOD-CANCEL-*))
     (3 3 (:REWRITE *-OF---ARG1))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (3 3 (:REWRITE |(* (- x) y)|))
     (2 2 (:LINEAR MOD-BOUNDS-3))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS)))
(FLOOR-WHEN-MOD-0
     (1009 5
           (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (944 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (409 409
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (225 3 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (214 4 (:LINEAR FLOOR-BOUNDS-3))
     (204 18 (:REWRITE CANCEL-FLOOR-+))
     (199 199 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (199 199 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (199 199 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (199 199
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (178 18 (:REWRITE FLOOR-ZERO . 4))
     (178 18 (:REWRITE FLOOR-ZERO . 3))
     (171 101 (:REWRITE DEFAULT-*-2))
     (132 104 (:REWRITE DEFAULT-<-2))
     (130 18 (:REWRITE FLOOR-WHEN-<))
     (123 123
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (123 22
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (119 119 (:REWRITE |(< (- x) (- y))|))
     (113 59 (:REWRITE DEFAULT-+-2))
     (104 104 (:REWRITE DEFAULT-<-1))
     (102 30 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (101 101
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (101 101 (:REWRITE DEFAULT-*-1))
     (91 91
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (69 18 (:REWRITE INTEGERP-OF-*))
     (65 65
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (65 65 (:REWRITE DEFAULT-UNARY-/))
     (64 22 (:REWRITE DEFAULT-UNARY-MINUS))
     (59 59
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (59 59 (:REWRITE DEFAULT-+-1))
     (54 4 (:LINEAR FLOOR-BOUNDS-2))
     (42 18
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (40 40 (:REWRITE INTEGERP-MINUS-X))
     (40 40 (:REWRITE |(< (- x) 0)|))
     (40 40 (:META META-INTEGERP-CORRECT))
     (39 39 (:REWRITE |(< 0 (- x))|))
     (38 38
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (37 37
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (34 4 (:REWRITE MOD-X-Y-=-X . 4))
     (34 4 (:REWRITE MOD-X-Y-=-X . 3))
     (34 3 (:REWRITE CANCEL-MOD-+))
     (33 3 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (32 2
         (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (30 30
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (30 30
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (30 30 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 30
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (30 30
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (30 30 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (30 30 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (30 30
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (30 30
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (30 30
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (30 30 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (29 4 (:REWRITE MOD-WHEN-MULTIPLE))
     (28 2 (:DEFINITION NATP))
     (26 4 (:REWRITE MOD-ZERO . 2))
     (26 1 (:LINEAR MOD-BOUNDS-3))
     (25 4 (:REWRITE MOD-WHEN-<))
     (22 22 (:REWRITE |(equal (- x) (- y))|))
     (22 4 (:REWRITE MOD-ZERO . 3))
     (20 2
         (:LINEAR MY-FLOOR-LOWER-BOUND-ALT-LINEAR))
     (20 2 (:LINEAR MOD-BOUNDS-2))
     (20 2 (:LINEAR MOD-BOUNDS-1))
     (20 2
         (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
     (18 18 (:REWRITE FLOOR-ZERO . 2))
     (18 18
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (18 18
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (18 18
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (18 18 (:REWRITE FLOOR-MINUS-WEAK))
     (18 18
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (18 18 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (18 18 (:REWRITE FLOOR-MINUS-2))
     (18 18 (:REWRITE FLOOR-COMPLETION))
     (18 18 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (18 18 (:REWRITE |(integerp (* c x))|))
     (15 15 (:REWRITE |(equal (- x) 0)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (11 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (10 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (8 8 (:REWRITE MOD-COMPLETION))
     (8 8 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (8 8
        (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (8 8 (:LINEAR <-OF-*-AND-*))
     (7 7 (:REWRITE |(< (+ c x) d)|))
     (7 7 (:REWRITE |(- (* c x))|))
     (5 5 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (5 5 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (5 5 (:REWRITE |(equal (+ c x) d)|))
     (5 5 (:REWRITE |(< d (+ c x))|))
     (4 4 (:REWRITE MOD-X-Y-=-X . 2))
     (4 4
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (4 4
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (4 4
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (4 4
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (4 1
        (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (3 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (3 3 (:REWRITE MOD-NEG))
     (3 3 (:REWRITE MOD-MINUS-2))
     (3 3 (:REWRITE MOD-CANCEL-*))
     (2 2 (:TYPE-PRESCRIPTION NATP))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE +-COMBINE-CONSTANTS))
     (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
     (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
     (2 2 (:REWRITE |(< (+ c x y) d)|))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT)))
(MOD-OF-*-SUBST-CONSTANT-ARG1
     (5123 48 (:REWRITE MOD-WHEN-MULTIPLE))
     (3027 21 (:REWRITE <-OF-*-AND-0))
     (2706 132
           (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (2694 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (2665 282 (:META META-INTEGERP-CORRECT))
     (2124 39 (:REWRITE CANCEL-MOD-+))
     (2043 39 (:REWRITE MOD-ZERO . 2))
     (2010 426 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2010 426
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1399 65 (:REWRITE |(* (* x y) z)|))
     (1286 39 (:REWRITE MOD-X-Y-=-X . 3))
     (1022 6 (:LINEAR MOD-BOUNDS-3))
     (991 65 (:REWRITE |(* y (* x z))|))
     (903 903
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (903 903
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (903 903
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (760 39 (:REWRITE MOD-ZERO . 3))
     (723 291 (:REWRITE DEFAULT-*-2))
     (623 39 (:REWRITE MOD-X-Y-=-X . 4))
     (611 39 (:REWRITE MOD-WHEN-<))
     (526 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (426 426
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (426 426
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (426 426
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (426 426
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (378 132 (:REWRITE INTEGERP-OF-*))
     (294 222 (:REWRITE SIMPLIFY-SUMS-<))
     (294 222
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (294 222
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (291 291
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (291 291 (:REWRITE DEFAULT-*-1))
     (282 282 (:REWRITE REDUCE-INTEGERP-+))
     (282 282 (:REWRITE INTEGERP-MINUS-X))
     (264 264
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (264 264
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (264 264
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (264 264
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (237 201 (:REWRITE DEFAULT-<-2))
     (236 89 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (222 222
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (222 222 (:REWRITE |(< (- x) (- y))|))
     (221 17 (:REWRITE |(equal (* x y) 0)|))
     (210 48
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (210 48
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (210 48
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (201 201 (:REWRITE DEFAULT-<-1))
     (197 197
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (197 197 (:REWRITE DEFAULT-UNARY-/))
     (178 178 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (178 178
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (178 178 (:LINEAR <-OF-*-AND-*))
     (163 163
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (132 132 (:REWRITE |(integerp (* c x))|))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (130 130 (:REWRITE |(* c (* d x))|))
     (89 89 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (89 89 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (89 89 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (89 89 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (86 2 (:REWRITE MOD-POSITIVE . 3))
     (84 84
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (84 84 (:REWRITE |(< (- x) 0)|))
     (84 12 (:LINEAR MOD-BOUNDS-2))
     (79 79
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (79 79 (:REWRITE |(< 0 (- x))|))
     (78 78 (:REWRITE MOD-COMPLETION))
     (65 65 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (55 55 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (55 55
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (55 55
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (55 55 (:REWRITE |(equal (- x) 0)|))
     (55 55 (:REWRITE |(equal (- x) (- y))|))
     (48 48
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (39 39 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (39 39 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (39 39 (:REWRITE MOD-X-Y-=-X . 2))
     (39 39 (:REWRITE MOD-NEG))
     (39 39 (:REWRITE MOD-MINUS-2))
     (39 39 (:REWRITE MOD-CANCEL-*))
     (34 34
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (30 30
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (30 30
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (21 21 (:REWRITE |(< (* x y) 0)|))
     (17 17 (:REWRITE |(< 0 (* x y))|))
     (13 13
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE MOD-POSITIVE . 2))
     (2 2 (:REWRITE MOD-POSITIVE . 1))
     (2 2 (:REWRITE MOD-NONPOSITIVE)))
(MOD-OF-*-SUBST-CONSTANT-ARG2
     (5911 60 (:REWRITE MOD-WHEN-MULTIPLE))
     (4913 9 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (3447 171
           (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (3340 26 (:REWRITE <-OF-*-AND-0))
     (2796 361 (:META META-INTEGERP-CORRECT))
     (2740 51 (:REWRITE CANCEL-MOD-+))
     (2659 51 (:REWRITE MOD-ZERO . 2))
     (2440 512 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2440 512
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2334 110
           (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (1773 78 (:REWRITE |(* (* x y) z)|))
     (1622 51 (:REWRITE MOD-X-Y-=-X . 3))
     (1219 9 (:LINEAR MOD-BOUNDS-3))
     (1107 78 (:REWRITE |(* y (* x z))|))
     (1102 1102
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1102 1102
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1102 1102
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (972 360 (:REWRITE DEFAULT-*-2))
     (960 51 (:REWRITE MOD-ZERO . 3))
     (803 51 (:REWRITE MOD-X-Y-=-X . 4))
     (779 51 (:REWRITE MOD-WHEN-<))
     (552 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (512 512
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (512 512
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (512 512
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (512 512
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (498 171 (:REWRITE INTEGERP-OF-*))
     (394 286 (:REWRITE SIMPLIFY-SUMS-<))
     (394 286
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (394 286
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (361 361 (:REWRITE REDUCE-INTEGERP-+))
     (361 361 (:REWRITE INTEGERP-MINUS-X))
     (360 360
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (360 360 (:REWRITE DEFAULT-*-1))
     (342 342
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (342 342
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (342 342
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (342 342
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (332 260 (:REWRITE DEFAULT-<-2))
     (286 286
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (286 286 (:REWRITE |(< (- x) (- y))|))
     (273 21 (:REWRITE |(equal (* x y) 0)|))
     (260 260 (:REWRITE DEFAULT-<-1))
     (249 249
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (249 249 (:REWRITE DEFAULT-UNARY-/))
     (222 60
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (222 60
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (222 60
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (220 220 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (220 220
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (220 220 (:LINEAR <-OF-*-AND-*))
     (210 210
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (171 171 (:REWRITE |(integerp (* c x))|))
     (156 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (156 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (156 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (156 156 (:REWRITE |(* c (* d x))|))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (109 109
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (109 109 (:REWRITE |(< (- x) 0)|))
     (102 102 (:REWRITE MOD-COMPLETION))
     (101 101
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (101 101 (:REWRITE |(< 0 (- x))|))
     (90 18 (:LINEAR MOD-BOUNDS-2))
     (86 2 (:REWRITE MOD-POSITIVE . 3))
     (78 78 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (71 71
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (71 71 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (71 71
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (71 71
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (71 71 (:REWRITE |(equal (- x) 0)|))
     (71 71 (:REWRITE |(equal (- x) (- y))|))
     (60 60
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (51 51 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (51 51 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (51 51 (:REWRITE MOD-X-Y-=-X . 2))
     (51 51 (:REWRITE MOD-NEG))
     (51 51 (:REWRITE MOD-MINUS-2))
     (51 51 (:REWRITE MOD-CANCEL-*))
     (34 34
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (31 31
         (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (30 30
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (30 30
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (21 21 (:REWRITE |(< 0 (* x y))|))
     (13 13
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE MOD-POSITIVE . 2))
     (2 2 (:REWRITE MOD-POSITIVE . 1))
     (2 2 (:REWRITE MOD-NONPOSITIVE)))
(INTEGERP-OF-*-OF-/-AND-MOD-SAME
     (554 14 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (268 9 (:REWRITE MOD-WHEN-MULTIPLE))
     (241 166
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (241 166
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (241 166
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (215 173 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (205 173 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (205 173
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (201 173
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (201 173
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (201 173
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (201 173
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (201 173
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (201 173 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (200 172
          (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (200 172
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (172 172
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (141 7 (:REWRITE CANCEL-MOD-+))
     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (60 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (60 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (60 15
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (49 7 (:REWRITE MOD-WHEN-<))
     (47 14 (:REWRITE INTEGERP-OF-*))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:REWRITE INTEGERP-MINUS-X))
     (34 34 (:META META-INTEGERP-CORRECT))
     (34 19 (:REWRITE DEFAULT-*-2))
     (28 16 (:REWRITE DEFAULT-UNARY-/))
     (19 19
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (19 19 (:REWRITE DEFAULT-*-1))
     (19 7 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (19 7 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (18 6
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (16 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (15 15 (:REWRITE |(equal (- x) 0)|))
     (15 15 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:REWRITE MOD-COMPLETION))
     (14 14 (:REWRITE |(integerp (* c x))|))
     (13 13 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 13
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (13 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 13 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-<-1))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:LINEAR MOD-BOUNDS-2))
     (12 12 (:LINEAR MOD-BOUNDS-1))
     (9 9
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (7 7 (:REWRITE MOD-ZERO . 3))
     (7 7 (:REWRITE MOD-ZERO . 2))
     (7 7 (:REWRITE MOD-X-Y-=-X . 4))
     (7 7 (:REWRITE MOD-X-Y-=-X . 3))
     (7 7 (:REWRITE MOD-X-Y-=-X . 2))
     (7 7
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (7 7
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (7 7 (:REWRITE MOD-NEG))
     (7 7 (:REWRITE MOD-MINUS-2))
     (7 7 (:REWRITE MOD-CANCEL-*))
     (6 6 (:LINEAR MOD-BOUNDS-3))
     (6 6 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (6 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (6 2
        (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
     (5 5
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (4 4 (:REWRITE |(< (- x) 0)|))
     (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (4 4 (:LINEAR <-OF-*-AND-*))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
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
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE MOD-ZERO . 1))
     (3 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (3 3 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1 (:REWRITE |(< 0 (- x))|)))
(MOD-WHEN-NOT-RATIONALP-OF-QUOTIENT
     (25 25
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (25 25 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (25 25
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (25 25
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (25 25
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (25 25
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (25 25 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (25 25 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (25 25
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (25 25
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (25 25
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (25 25 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (25 4 (:REWRITE DEFAULT-UNARY-/))
     (18 1 (:REWRITE MOD-WHEN-MULTIPLE))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (14 1 (:REWRITE CANCEL-FLOOR-+))
     (8 2
        (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (8 1 (:REWRITE MOD-WHEN-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (7 7
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (7 1 (:REWRITE CANCEL-MOD-+))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (6 6 (:REWRITE |(equal (- x) 0)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:LINEAR MOD-BOUNDS-2))
     (4 4 (:LINEAR MOD-BOUNDS-1))
     (3 1 (:REWRITE FLOOR-COMPLETION))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 2 (:LINEAR MOD-BOUNDS-3))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (2 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE MOD-ZERO . 3))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE MOD-X-Y-=-X . 4))
     (1 1 (:REWRITE MOD-X-Y-=-X . 3))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE FLOOR-ZERO . 4))
     (1 1 (:REWRITE FLOOR-ZERO . 3))
     (1 1 (:REWRITE FLOOR-ZERO . 2))
     (1 1 (:REWRITE FLOOR-MINUS-WEAK))
     (1 1 (:REWRITE FLOOR-MINUS-2))
     (1 1 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE |(equal (+ c x) d)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(+ 0 x)|)))
(MOD-WHEN-INTEGERP-OF-QUOTIENT
     (26 26
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (26 26 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (26 26
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (26 26
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (26 26 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (26 26 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (26 26
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (26 26
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (26 26 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (26 26 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (26 26
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (26 26
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (26 26
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (26 26 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (24 3 (:REWRITE DEFAULT-UNARY-/))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (13 1 (:REWRITE CANCEL-FLOOR-+))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 9
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 9 (:REWRITE |(equal (- x) 0)|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (8 1 (:REWRITE MOD-WHEN-<))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (7 1 (:REWRITE CANCEL-MOD-+))
     (4 1 (:REWRITE INTEGERP-OF-*))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3 3 (:REWRITE DEFAULT-*-2))
     (3 3 (:REWRITE DEFAULT-*-1))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE MOD-COMPLETION))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE FLOOR-COMPLETION))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE MOD-ZERO . 3))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE MOD-X-Y-=-X . 4))
     (1 1 (:REWRITE MOD-X-Y-=-X . 3))
     (1 1 (:REWRITE MOD-X-Y-=-X . 2))
     (1 1
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (1 1
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (1 1 (:REWRITE MOD-WHEN-MULTIPLE))
     (1 1 (:REWRITE MOD-NEG))
     (1 1 (:REWRITE MOD-MINUS-2))
     (1 1 (:REWRITE MOD-CANCEL-*))
     (1 1 (:REWRITE FLOOR-ZERO . 4))
     (1 1 (:REWRITE FLOOR-ZERO . 3))
     (1 1 (:REWRITE FLOOR-ZERO . 2))
     (1 1
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (1 1 (:REWRITE FLOOR-MINUS-WEAK))
     (1 1 (:REWRITE FLOOR-MINUS-2))
     (1 1 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE |(integerp (* c x))|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(* a (/ a))|)))
(MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE
     (1117 925 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1029 925
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1013 925
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (925 925
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (925 925
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (925 925
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (925 925 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (903 903
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (903 903
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (856 856
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (634 32 (:REWRITE MOD-WHEN-MULTIPLE))
     (542 183
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (527 527
          (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (452 183 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (452 183
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (313 28 (:REWRITE MOD-WHEN-<))
     (225 43 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (206 166 (:REWRITE DEFAULT-*-2))
     (196 28 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (196 28 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (196 28 (:REWRITE CANCEL-MOD-+))
     (190 110 (:REWRITE DEFAULT-+-2))
     (183 183
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (183 183 (:REWRITE |(equal (- x) 0)|))
     (183 183 (:REWRITE |(equal (- x) (- y))|))
     (176 43
          (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (173 173
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (166 166
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (166 166 (:REWRITE DEFAULT-*-1))
     (163 115 (:META META-INTEGERP-CORRECT))
     (158 86 (:LINEAR MOD-BOUNDS-2))
     (158 86 (:LINEAR MOD-BOUNDS-1))
     (155 155
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (147 147 (:REWRITE |(< (- x) (- y))|))
     (142 110 (:REWRITE DEFAULT-+-1))
     (139 139
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (123 123 (:REWRITE DEFAULT-<-2))
     (123 123 (:REWRITE DEFAULT-<-1))
     (115 115 (:REWRITE INTEGERP-MINUS-X))
     (110 110
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (103 103
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (98 98
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (96 4
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (90 28 (:REWRITE MOD-ZERO . 3))
     (86 28 (:REWRITE MOD-X-Y-=-X . 4))
     (86 28 (:REWRITE MOD-X-Y-=-X . 3))
     (79 43 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (67 43 (:LINEAR MOD-BOUNDS-3))
     (61 61 (:REWRITE |(integerp (* c x))|))
     (56 56 (:REWRITE MOD-COMPLETION))
     (49 49 (:REWRITE |(< (- x) 0)|))
     (46 28 (:REWRITE MOD-ZERO . 2))
     (45 45
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (42 24
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (42 4
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (39 39 (:REWRITE |(< 0 (- x))|))
     (35 35
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (33 12 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (30 12 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (30 12 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (28 28 (:REWRITE MOD-X-Y-=-X . 2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (28 28
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (28 28 (:REWRITE MOD-NEG))
     (28 28 (:REWRITE MOD-MINUS-2))
     (28 28 (:REWRITE MOD-CANCEL-*))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
     (25 25 (:REWRITE MOD-ZERO . 1))
     (25 25 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (24 24 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (24 24 (:LINEAR <-OF-*-AND-*))
     (22 2 (:REWRITE MOD-SUM-CASES))
     (18 18 (:REWRITE |(< (+ c x) d)|))
     (12 12 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (12 12 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (12 4
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (11 11 (:REWRITE |(* c (* d x))|))
     (10 10 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (10 10 (:REWRITE |(< d (+ c x))|))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (6 6
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (6 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (6 6
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4P))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4J))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4F))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3P))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3J))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3F))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2P))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2J))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2F))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1P))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1J))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1F))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (4 4
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (4 4 (:REWRITE +-COMBINE-CONSTANTS))
     (4 4 (:REWRITE |(equal (+ c x) d)|))
     (4 4 (:REWRITE |(< (+ d x) (+ c y))|))
     (4 4 (:REWRITE |(< (+ c x) (+ d y))|))
     (4 4 (:REWRITE |(< (+ c x y) d)|))
     (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (2 2
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP
     (80 2
         (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (70 70
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (70 70
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (70 70 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (70 70 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (70 70
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (70 70
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (70 70 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (70 70 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (70 70
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (70 70
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (70 70
         (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (70 70 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (61 2 (:REWRITE MOD-WHEN-MULTIPLE))
     (53 53
         (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (38 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (38 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (38 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (28 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (17 4 (:REWRITE DEFAULT-UNARY-/))
     (16 4
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (16 2 (:REWRITE MOD-WHEN-<))
     (14 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (14 2 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (14 2 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (14 2 (:REWRITE CANCEL-MOD-+))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:REWRITE |(equal (- x) 0)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (10 10 (:META META-INTEGERP-CORRECT))
     (10 4 (:REWRITE INTEGERP-OF-*))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (8 8 (:LINEAR MOD-BOUNDS-2))
     (8 8 (:LINEAR MOD-BOUNDS-1))
     (8 2 (:REWRITE |(* y x)|))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE MOD-COMPLETION))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:REWRITE |(integerp (* c x))|))
     (4 4 (:LINEAR MOD-BOUNDS-3))
     (4 4 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE MOD-ZERO . 3))
     (2 2 (:REWRITE MOD-ZERO . 2))
     (2 2 (:REWRITE MOD-ZERO . 1))
     (2 2 (:REWRITE MOD-X-Y-=-X . 4))
     (2 2 (:REWRITE MOD-X-Y-=-X . 3))
     (2 2 (:REWRITE MOD-X-Y-=-X . 2))
     (2 2
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (2 2
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (2 2
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (2 2
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (2 2 (:REWRITE MOD-NEG))
     (2 2 (:REWRITE MOD-MINUS-2))
     (2 2 (:REWRITE MOD-CANCEL-*))
     (2 2 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1 1 (:REWRITE |(< (- x) 0)|)))
(MOD-OF-MOD-WHEN-MULTIPLE
     (3503 1645 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3452 1646
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (3400 61 (:REWRITE MOD-WHEN-MULTIPLE))
     (2806 2716
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2806 2716
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2214 19 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (2164 1646
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2164 1646
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2164 1646
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2163 1645
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (2163 1645
           (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (2163 1645 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (2074 37 (:REWRITE CANCEL-MOD-+))
     (1842 1324
           (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (1814 1296
           (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (1526 430 (:REWRITE DEFAULT-+-2))
     (1324 1324
           (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (1253 420 (:META META-INTEGERP-CORRECT))
     (1034 711 (:REWRITE DEFAULT-*-2))
     (931 526
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (906 200 (:REWRITE INTEGERP-OF-*))
     (811 18 (:LINEAR MOD-BOUNDS-3))
     (789 42
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (789 42
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (788 36 (:LINEAR MOD-BOUNDS-2))
     (743 35
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
     (711 711
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (711 711 (:REWRITE DEFAULT-*-1))
     (661 526
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (634 430 (:REWRITE DEFAULT-+-1))
     (622 21
          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
     (598 18
          (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (433 37 (:REWRITE MOD-ZERO . 2))
     (430 430
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (420 420 (:REWRITE INTEGERP-MINUS-X))
     (376 376
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (376 376
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (372 10 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (358 37 (:REWRITE MOD-X-Y-=-X . 4))
     (304 304
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (304 304 (:REWRITE DEFAULT-UNARY-/))
     (296 36
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (262 37 (:REWRITE MOD-ZERO . 3))
     (261 261 (:REWRITE |(< (- x) (- y))|))
     (243 198 (:REWRITE DEFAULT-<-1))
     (226 198 (:REWRITE DEFAULT-<-2))
     (202 61
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (201 201
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (201 201
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (201 201
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (201 201
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (200 200 (:REWRITE |(integerp (* c x))|))
     (178 37 (:REWRITE MOD-NEG))
     (178 37 (:REWRITE MOD-MINUS-2))
     (178 37 (:REWRITE MOD-CANCEL-*))
     (175 37 (:REWRITE MOD-X-Y-=-X . 3))
     (166 166 (:REWRITE |(* c (* d x))|))
     (146 5 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (136 136 (:REWRITE FOLD-CONSTS-IN-+))
     (136 136 (:REWRITE +-COMBINE-CONSTANTS))
     (119 74 (:REWRITE MOD-COMPLETION))
     (110 110 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (103 58
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (89 7
         (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
     (86 86
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (86 86 (:REWRITE |(< 0 (- x))|))
     (80 80 (:REWRITE RATIONALP-OF-MOD))
     (80 80 (:REWRITE RATIONALP-MOD))
     (72 20
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (62 10 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (59 59 (:REWRITE |(< (- x) 0)|))
     (58 58
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (57 57 (:REWRITE DEFAULT-UNARY-MINUS))
     (52 37 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (43 43 (:REWRITE |(< (+ c x) d)|))
     (42 42 (:REWRITE |(equal (- x) (- y))|))
     (40 40
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (37 37 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (37 37 (:REWRITE MOD-X-Y-=-X . 2))
     (36 36 (:REWRITE |(equal (- x) 0)|))
     (32 8 (:REWRITE INTEGERP-OF-MOD))
     (28 10 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (26 8 (:REWRITE INTEGERP-MOD))
     (25 25 (:REWRITE |(< d (+ c x))|))
     (20 20 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (20 20 (:LINEAR <-OF-*-AND-*))
     (20 4
         (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
     (17 17
         (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (17 17
         (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (17 17 (:REWRITE |(< (+ c x y) d)|))
     (15 3 (:REWRITE |(* (if a b c) x)|))
     (10 10 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (10 10 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (8 1 (:REWRITE |(< (if a b c) x)|))
     (7 7 (:REWRITE |(< (+ d x) (+ c y))|))
     (7 7 (:REWRITE |(< (+ c x) (+ d y))|))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (6 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (6 6
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (6 6 (:REWRITE |(equal (+ c x) d)|))
     (4 4
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (4 4
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (4 4 (:REWRITE |(< d (+ c x y))|))
     (3 3 (:REWRITE REWRITE-MOD-MOD-WEAK))
     (2 2 (:REWRITE |(equal (+ c x y) d)|))
     (1 1 (:REWRITE MOD-X-Y-=-X . 1))
     (1 1 (:REWRITE EQUAL-OF-MOD-SAME-ARG1)))
(MOD-OF-MOD-WHEN-MULTIPLE-SAFE (24 16 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                               (24 16
                                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                               (16 16
                                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                               (16 16 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                               (16 16
                                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                               (16 16
                                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                               (16 16
                                   (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                               (16 16 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                               (14 14
                                   (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                               (14 14
                                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                               (14 14
                                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                               (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                               (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                               (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                               (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
