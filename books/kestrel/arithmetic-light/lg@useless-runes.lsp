(INTEGER-LENGTH-OF-EXPT2
     (123 4 (:REWRITE FLOOR-TYPE-3 . 2))
     (118 5 (:REWRITE FLOOR-WHEN-<))
     (110 16 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (86 4 (:REWRITE FLOOR-=-X/Y . 3))
     (74 28 (:REWRITE DEFAULT-*-2))
     (68 4 (:REWRITE FLOOR-=-X/Y . 2))
     (49 33 (:REWRITE DEFAULT-<-1))
     (44 28 (:REWRITE DEFAULT-*-1))
     (40 8 (:REWRITE COMMUTATIVITY-OF-*))
     (35 31 (:REWRITE DEFAULT-+-2))
     (33 33 (:REWRITE DEFAULT-<-2))
     (33 11 (:REWRITE COMMUTATIVITY-OF-+))
     (31 31 (:REWRITE DEFAULT-+-1))
     (26 8 (:REWRITE EXPT-INTEGER-HACK))
     (18 6
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (18 6
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (16 16 (:LINEAR EXPT-BOUND-LINEAR))
     (15 5
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (15 5
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (14 4 (:DEFINITION POSP))
     (12 4 (:REWRITE FLOOR-TYPE-4 . 3))
     (12 4 (:REWRITE FLOOR-TYPE-4 . 2))
     (12 4 (:REWRITE FLOOR-TYPE-3 . 3))
     (6 6 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
     (5 5
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (5 5 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (4 4 (:TYPE-PRESCRIPTION POSP))
     (2 2
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:REWRITE EQUAL-CONSTANT-+))
     (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (1 1
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(INTEGER-LENGTH-OF-MASK (38 2
                            (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
                        (26 1 (:REWRITE FLOOR-=-X/Y . 3))
                        (22 11 (:REWRITE DEFAULT-+-2))
                        (20 2 (:REWRITE FLOOR-WHEN-<))
                        (19 9 (:REWRITE DEFAULT-*-2))
                        (19 1 (:REWRITE FLOOR-TYPE-3 . 2))
                        (17 9 (:REWRITE DEFAULT-*-1))
                        (15 7 (:REWRITE DEFAULT-<-1))
                        (15 5
                            (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                        (11 11 (:REWRITE DEFAULT-+-1))
                        (9 3
                           (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                        (8 8 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
                        (8 8 (:LINEAR EXPT-BOUND-LINEAR))
                        (7 7 (:REWRITE DEFAULT-<-2))
                        (7 1 (:REWRITE EQUAL-OF-1-AND-EXPT))
                        (6 2
                           (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
                        (6 2
                           (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
                        (6 2
                           (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
                        (6 2
                           (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                        (6 2
                           (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                        (6 2 (:REWRITE EXPT-INTEGER-HACK))
                        (3 3
                           (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                        (3 3 (:REWRITE EQUAL-CONSTANT-+))
                        (3 1 (:REWRITE FLOOR-TYPE-4 . 3))
                        (3 1 (:REWRITE FLOOR-TYPE-4 . 2))
                        (3 1 (:REWRITE FLOOR-TYPE-3 . 3))
                        (2 2 (:TYPE-PRESCRIPTION POSP))
                        (2 2
                           (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                        (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                        (2 2 (:DEFINITION POSP))
                        (2 1 (:REWRITE INVERSE-OF-+-AS=0))
                        (1 1 (:DEFINITION IFIX)))
(DOUBLE-FLOOR-BY-2-INDUCT (48 8 (:REWRITE FLOOR-=-X/Y . 3))
                          (48 8 (:REWRITE FLOOR-=-X/Y . 2))
                          (42 42 (:REWRITE DEFAULT-*-2))
                          (42 42 (:REWRITE DEFAULT-*-1))
                          (29 29
                              (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
                          (29 29
                              (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
                          (29 17 (:REWRITE DEFAULT-<-1))
                          (25 8 (:REWRITE FLOOR-TYPE-4 . 3))
                          (17 17
                              (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
                          (17 17
                              (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
                          (17 17 (:REWRITE DEFAULT-<-2))
                          (14 8 (:REWRITE FLOOR-WHEN-<))
                          (14 8 (:REWRITE FLOOR-TYPE-3 . 2))
                          (13 7 (:REWRITE DEFAULT-UNARY-MINUS))
                          (10 8 (:REWRITE FLOOR-TYPE-4 . 2))
                          (10 8 (:REWRITE FLOOR-TYPE-3 . 3))
                          (8 8
                             (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                          (8 8
                             (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                          (8 8
                             (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                          (8 8
                             (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                          (8 8
                             (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                          (8 8 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                          (2 2 (:REWRITE ZIP-OPEN))
                          (1 1 (:REWRITE DEFAULT-+-2))
                          (1 1 (:REWRITE DEFAULT-+-1))
                          (1 1 (:LINEAR FLOOR-TYPE-2 . 2))
                          (1 1 (:LINEAR FLOOR-TYPE-2 . 1))
                          (1 1 (:LINEAR FLOOR-TYPE-1 . 2)))
(INTEGER-LENGTH-MONOTONIC
     (1014 42 (:REWRITE FLOOR-WHEN-<))
     (312 8 (:LINEAR FLOOR-BOUNDED-BY-/))
     (252 84 (:REWRITE COMMUTATIVITY-OF-*))
     (208 38 (:REWRITE FLOOR-=-X/Y . 3))
     (208 38 (:REWRITE FLOOR-=-X/Y . 2))
     (168 168 (:REWRITE DEFAULT-*-2))
     (168 168 (:REWRITE DEFAULT-*-1))
     (164 4 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
     (158 158
          (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (158 158
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (158 158
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (158 158
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (144 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (140 4 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (120 4 (:LINEAR FLOOR-TYPE-2 . 1))
     (112 4 (:REWRITE FLOOR-OF-FLOOR))
     (82 6 (:REWRITE ZIP-OPEN))
     (72 72
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (72 72
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
     (66 42
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (66 42
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (66 42
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (58 38 (:REWRITE FLOOR-TYPE-3 . 2))
     (43 41 (:REWRITE DEFAULT-<-2))
     (43 41 (:REWRITE DEFAULT-<-1))
     (42 42
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (42 42 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (38 38
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (38 38 (:REWRITE FLOOR-TYPE-4 . 3))
     (38 38 (:REWRITE FLOOR-TYPE-4 . 2))
     (38 38 (:REWRITE FLOOR-TYPE-3 . 3))
     (28 4 (:REWRITE EQUAL-OF-0-AND-FLOOR))
     (20 12 (:REWRITE DEFAULT-+-2))
     (13 5
         (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
     (12 12 (:REWRITE DEFAULT-+-1))
     (4 4 (:LINEAR FLOOR-TYPE-2 . 2))
     (4 4 (:LINEAR FLOOR-TYPE-1 . 2))
     (4 4 (:LINEAR FLOOR-TYPE-1 . 1))
     (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (1 1
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (1 1
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(INTEGER-LENGTH-OF-TIMES-2
     (12 4 (:REWRITE COMMUTATIVITY-OF-*))
     (12 2 (:REWRITE FLOOR-=-X/Y . 3))
     (12 2 (:REWRITE FLOOR-=-X/Y . 2))
     (10 5 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-*-2))
     (9 9 (:REWRITE DEFAULT-*-1))
     (7 3 (:REWRITE FLOOR-WHEN-<))
     (6 2 (:REWRITE FLOOR-TYPE-3 . 2))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (5 5 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (4 4
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (3 3
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (3 3
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (3 3
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (3 3 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (2 2 (:REWRITE FLOOR-TYPE-4 . 3))
     (2 2 (:REWRITE FLOOR-TYPE-4 . 2))
     (2 2 (:REWRITE FLOOR-TYPE-3 . 3)))
(INTEGER-LENGTH-OF-FLOOR-BY-2
     (501 19 (:REWRITE FLOOR-WHEN-<))
     (156 4 (:LINEAR FLOOR-BOUNDED-BY-/))
     (114 38 (:REWRITE COMMUTATIVITY-OF-*))
     (92 17 (:REWRITE FLOOR-=-X/Y . 3))
     (92 17 (:REWRITE FLOOR-=-X/Y . 2))
     (82 2 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
     (76 76 (:REWRITE DEFAULT-*-2))
     (76 76 (:REWRITE DEFAULT-*-1))
     (72 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (70 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (60 2 (:LINEAR FLOOR-TYPE-2 . 1))
     (56 2 (:REWRITE FLOOR-OF-FLOOR))
     (42 2 (:REWRITE ZIP-OPEN))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (38 38 (:TYPE-PRESCRIPTION FLOOR))
     (31 19
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (31 19
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (31 19
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (23 17 (:REWRITE FLOOR-TYPE-3 . 2))
     (19 19
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (19 19 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (17 17
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (17 17 (:REWRITE FLOOR-TYPE-4 . 3))
     (17 17 (:REWRITE FLOOR-TYPE-4 . 2))
     (17 17 (:REWRITE FLOOR-TYPE-3 . 3))
     (16 2 (:REWRITE EQUAL-OF-0-AND-FLOOR))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (12 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 2
        (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
     (2 2 (:LINEAR FLOOR-TYPE-2 . 2))
     (2 2 (:LINEAR FLOOR-TYPE-1 . 2))
     (2 2 (:LINEAR FLOOR-TYPE-1 . 1)))
(FLOOR-BY-2-BOUND-EVEN-LINEAR
     (217 217
          (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (217 217
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (217 217
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (217 217
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (93 93
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (93 93
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
     (41 29 (:REWRITE DEFAULT-<-1))
     (29 29 (:REWRITE DEFAULT-<-2))
     (26 26 (:REWRITE DEFAULT-*-2))
     (26 26 (:REWRITE DEFAULT-*-1))
     (16 6 (:REWRITE FLOOR-WHEN-<))
     (16 6 (:REWRITE FLOOR-TYPE-3 . 3))
     (16 6 (:REWRITE FLOOR-TYPE-3 . 2))
     (12 6 (:REWRITE FLOOR-TYPE-4 . 2))
     (12 2 (:REWRITE FLOOR-=-X/Y . 2))
     (6 6
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (6 6
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (6 6
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (6 6
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (6 6 (:REWRITE FLOOR-TYPE-4 . 3))
     (6 6
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (6 6 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (2 2
        (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN)))
(<-OF-1-AND-FLOOR-OF-2
     (63 63
         (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (63 63
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (63 63
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (63 63
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (51 27 (:REWRITE DEFAULT-<-2))
     (37 7 (:REWRITE FLOOR-=-X/Y . 3))
     (37 7 (:REWRITE FLOOR-=-X/Y . 2))
     (27 27 (:REWRITE DEFAULT-<-1))
     (26 26 (:REWRITE DEFAULT-*-2))
     (26 26 (:REWRITE DEFAULT-*-1))
     (17 7 (:REWRITE FLOOR-WHEN-<))
     (15 7 (:REWRITE FLOOR-TYPE-4 . 2))
     (15 7 (:REWRITE FLOOR-TYPE-3 . 3))
     (15 7 (:REWRITE FLOOR-TYPE-3 . 2))
     (7 7
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (7 7
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (7 7
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (7 7
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (7 7 (:REWRITE FLOOR-TYPE-4 . 3))
     (7 7
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (7 7 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (4 4 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (4 4
        (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1)))
(EQUAL-OF-0-AND-INTEGER-LENGTH
     (6 2 (:REWRITE COMMUTATIVITY-OF-*))
     (6 1 (:REWRITE FLOOR-=-X/Y . 3))
     (6 1 (:REWRITE FLOOR-=-X/Y . 2))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 1 (:REWRITE FLOOR-WHEN-<))
     (3 1 (:REWRITE FLOOR-TYPE-3 . 2))
     (2 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE ZIP-OPEN))
     (1 1
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (1 1
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (1 1
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (1 1
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (1 1 (:REWRITE FLOOR-TYPE-4 . 3))
     (1 1 (:REWRITE FLOOR-TYPE-4 . 2))
     (1 1 (:REWRITE FLOOR-TYPE-3 . 3))
     (1 1
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (1 1 (:REWRITE DEFAULT-+-1)))
(EQUAL-OF-1-AND-INTEGER-LENGTH
     (12 4 (:REWRITE COMMUTATIVITY-OF-*))
     (12 2 (:REWRITE FLOOR-=-X/Y . 3))
     (12 2 (:REWRITE FLOOR-=-X/Y . 2))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (8 8 (:REWRITE DEFAULT-*-2))
     (8 8 (:REWRITE DEFAULT-*-1))
     (6 2 (:REWRITE FLOOR-WHEN-<))
     (6 2 (:REWRITE FLOOR-TYPE-3 . 2))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2
        (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (2 2
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (2 2 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (2 2 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (2 2 (:REWRITE ZIP-OPEN))
     (2 2
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (2 2
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (2 2
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (2 2
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (2 2 (:REWRITE FLOOR-TYPE-4 . 3))
     (2 2 (:REWRITE FLOOR-TYPE-4 . 2))
     (2 2 (:REWRITE FLOOR-TYPE-3 . 3))
     (2 2
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT)))
(<-OF-1-AND-INTEGER-LENGTH
     (90 15 (:REWRITE FLOOR-=-X/Y . 3))
     (90 15 (:REWRITE FLOOR-=-X/Y . 2))
     (82 82 (:REWRITE DEFAULT-*-2))
     (82 82 (:REWRITE DEFAULT-*-1))
     (53 53
         (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (53 53
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (53 53
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
     (53 53
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
     (45 15 (:REWRITE FLOOR-WHEN-<))
     (45 15 (:REWRITE FLOOR-TYPE-3 . 2))
     (44 40 (:REWRITE DEFAULT-<-2))
     (40 40 (:REWRITE DEFAULT-<-1))
     (19 19
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
     (19 19
         (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
     (16 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
     (15 15
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (15 15
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (15 15
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (15 15
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (15 15 (:REWRITE FLOOR-TYPE-4 . 3))
     (15 15 (:REWRITE FLOOR-TYPE-4 . 2))
     (15 15 (:REWRITE FLOOR-TYPE-3 . 3))
     (15 15
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (15 15 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (10 7 (:REWRITE DEFAULT-+-2))
     (8 1 (:REWRITE FLOOR-=-X/Y . 4))
     (7 7 (:REWRITE DEFAULT-+-1))
     (3 1
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (2 2
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (2 2 (:LINEAR FLOOR-TYPE-2 . 2))
     (2 2 (:LINEAR FLOOR-TYPE-1 . 2))
     (2 2 (:LINEAR FLOOR-TYPE-1 . 1))
     (2 2
        (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
     (2 1 (:REWRITE EQUAL-*-/-1))
     (1 1 (:DEFINITION FIX)))
(LG)
(LG-OF-EXPT (2 2 (:REWRITE DEFAULT-<-2))
            (2 2 (:REWRITE DEFAULT-<-1))
            (2 2 (:REWRITE DEFAULT-+-2))
            (2 2 (:REWRITE DEFAULT-+-1)))
(LG-OF-BOTH-SIDES)
(EQUAL-OF-EXPT-AND-CONSTANT
     (39 39 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (39 39
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(EQUAL-OF-0-AND-LG (32 1 (:DEFINITION INTEGER-LENGTH))
                   (6 2 (:REWRITE COMMUTATIVITY-OF-*))
                   (6 1 (:REWRITE FLOOR-=-X/Y . 3))
                   (6 1 (:REWRITE FLOOR-=-X/Y . 2))
                   (4 4 (:REWRITE DEFAULT-*-2))
                   (4 4 (:REWRITE DEFAULT-*-1))
                   (4 2 (:REWRITE DEFAULT-+-2))
                   (3 3 (:REWRITE DEFAULT-<-2))
                   (3 3 (:REWRITE DEFAULT-<-1))
                   (3 1 (:REWRITE FLOOR-WHEN-<))
                   (3 1 (:REWRITE FLOOR-TYPE-3 . 2))
                   (2 2 (:REWRITE DEFAULT-+-1))
                   (1 1 (:REWRITE ZIP-OPEN))
                   (1 1
                      (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                   (1 1
                      (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                   (1 1
                      (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                   (1 1
                      (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                   (1 1 (:REWRITE FLOOR-TYPE-4 . 3))
                   (1 1 (:REWRITE FLOOR-TYPE-4 . 2))
                   (1 1 (:REWRITE FLOOR-TYPE-3 . 3))
                   (1 1
                      (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                   (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER)))
(NATP-OF-LG (9 7 (:REWRITE DEFAULT-<-1))
            (7 7 (:REWRITE DEFAULT-<-2))
            (2 1 (:REWRITE DEFAULT-+-2))
            (1 1 (:REWRITE DEFAULT-+-1)))
(POSP-OF-LG (8 8 (:REWRITE DEFAULT-<-2))
            (8 8 (:REWRITE DEFAULT-<-1))
            (6 2 (:REWRITE COMMUTATIVITY-OF-*))
            (6 1 (:REWRITE FLOOR-=-X/Y . 3))
            (6 1 (:REWRITE FLOOR-=-X/Y . 2))
            (5 3 (:REWRITE DEFAULT-+-2))
            (4 4 (:REWRITE DEFAULT-*-2))
            (4 4 (:REWRITE DEFAULT-*-1))
            (3 3 (:REWRITE DEFAULT-+-1))
            (3 1 (:REWRITE FLOOR-TYPE-3 . 2))
            (2 2
               (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
            (2 2
               (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
            (2 2
               (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
            (2 2
               (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
            (1 1 (:REWRITE ZIP-OPEN))
            (1 1
               (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
            (1 1 (:REWRITE FLOOR-TYPE-4 . 3))
            (1 1 (:REWRITE FLOOR-TYPE-4 . 2))
            (1 1 (:REWRITE FLOOR-TYPE-3 . 3))
            (1 1 (:REWRITE FLOOR-MINUS-ERIC-BETTER)))
(EXPT-OF-LG (4 4 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
            (4 4
               (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
            (4 4
               (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP)))
