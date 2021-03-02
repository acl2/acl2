(INTEGERP-OF-*-OF---ARG2 (3 2 (:REWRITE DEFAULT-*-2))
                         (3 2 (:REWRITE DEFAULT-*-1))
                         (2 2
                            (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                         (1 1 (:REWRITE INTEGERP-OF-*))
                         (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(CEILING-OF-0)
(CEILING-IN-TERMS-OF-FLOOR
     (380 24
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (133 61 (:REWRITE DEFAULT-UNARY-/))
     (132 92 (:REWRITE DEFAULT-+-2))
     (100 94 (:REWRITE DEFAULT-<-2))
     (100 92 (:REWRITE DEFAULT-+-1))
     (94 94 (:REWRITE DEFAULT-<-1))
     (83 59 (:REWRITE DEFAULT-*-1))
     (80 80
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (72 24 (:DEFINITION NFIX))
     (71 55 (:REWRITE DEFAULT-UNARY-MINUS))
     (59 59 (:REWRITE DEFAULT-*-2))
     (27 7 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
     (24 24 (:DEFINITION IFIX))
     (24 16 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (24 16
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (24 8 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (22 20 (:REWRITE DEFAULT-NUMERATOR))
     (20 18 (:REWRITE DEFAULT-DENOMINATOR))
     (19 19 (:REWRITE INTEGERP-OF-*))
     (16 16 (:LINEAR <-OF-*-AND-*))
     (14 14 (:REWRITE RATIONALP-*))
     (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (3 3 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
     (3 3 (:REWRITE EQUAL-OF---AND-CONSTANT))
     (3 2
        (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR)))
(CEILING-WHEN-<= (14 14 (:REWRITE DEFAULT-<-2))
                 (14 14 (:REWRITE DEFAULT-<-1))
                 (12 12 (:REWRITE DEFAULT-*-2))
                 (12 12 (:REWRITE DEFAULT-*-1))
                 (11 11 (:REWRITE DEFAULT-UNARY-/))
                 (9 9
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                 (9 9
                    (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                 (9 9
                    (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                 (9 9
                    (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                 (9 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                 (6 6
                    (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                 (6 6 (:LINEAR <-OF-*-AND-*))
                 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                 (2 2 (:REWRITE INTEGERP-OF-*))
                 (2 2
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                 (2 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR)))
(CEILING-OF-+-OF-MINUS-8 (120 48 (:REWRITE DEFAULT-+-2))
                         (84 84
                             (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                         (84 84
                             (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                         (63 15 (:REWRITE DEFAULT-UNARY-MINUS))
                         (52 48 (:REWRITE DEFAULT-+-1))
                         (46 15 (:REWRITE FLOOR-WHEN-<))
                         (18 18
                             (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                         (18 18
                             (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                         (18 18
                             (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                         (18 18
                             (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                         (17 17 (:REWRITE DEFAULT-<-2))
                         (17 17 (:REWRITE DEFAULT-<-1))
                         (17 17 (:REWRITE DEFAULT-*-2))
                         (17 17 (:REWRITE DEFAULT-*-1))
                         (8 8
                            (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                         (6 6 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
                         (6 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                         (3 1 (:REWRITE <-OF-MINUS-AND-CONSTANT))
                         (1 1 (:REWRITE INTEGERP-OF-*))
                         (1 1 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
                         (1 1 (:REWRITE EQUAL-OF---AND-CONSTANT)))
(CEILING-IN-TERMS-OF-FLOOR-CASES
     (66 4
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (25 17 (:REWRITE DEFAULT-+-2))
     (19 17 (:REWRITE DEFAULT-+-1))
     (18 18 (:REWRITE DEFAULT-<-2))
     (18 18 (:REWRITE DEFAULT-<-1))
     (12 4 (:DEFINITION NFIX))
     (10 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 2 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
     (4 4 (:REWRITE INTEGERP-OF-*))
     (4 4 (:REWRITE DEFAULT-UNARY-/))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:DEFINITION IFIX))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (3 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (3 2 (:REWRITE DENOMINATOR-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 2 (:REWRITE <-OF-MINUS-AND-CONSTANT)))
(CEILING-UPPER-BOUND (381 381
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                     (381 381
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                     (253 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                     (251 7 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                     (125 45 (:REWRITE DEFAULT-*-2))
                     (114 74 (:REWRITE DEFAULT-<-2))
                     (112 16
                          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                     (101 33 (:REWRITE FLOOR-WHEN-<))
                     (96 96 (:TYPE-PRESCRIPTION MOD))
                     (92 74 (:REWRITE DEFAULT-<-1))
                     (59 45 (:REWRITE DEFAULT-*-1))
                     (53 13 (:REWRITE DEFAULT-UNARY-MINUS))
                     (50 26 (:REWRITE DEFAULT-+-2))
                     (43 33
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                     (35 33
                         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                     (34 26 (:REWRITE DEFAULT-+-1))
                     (34 11 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                     (33 33
                         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                     (33 33
                         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                     (31 31
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                     (25 5
                         (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
                     (22 22 (:REWRITE DEFAULT-UNARY-/))
                     (15 5 (:DEFINITION NATP))
                     (14 14 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                     (14 14
                         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                     (14 14 (:LINEAR <-OF-*-AND-*))
                     (7 7 (:REWRITE INTEGERP-OF-*))
                     (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                     (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                     (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                     (6 6
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (5 5 (:TYPE-PRESCRIPTION NATP))
                     (5 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
                     (4 4 (:REWRITE <-OF-0-AND-FLOOR))
                     (3 3 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
                     (2 2 (:REWRITE RATIONALP-*)))
(CEILING-LOWER-BOUND (256 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                     (216 216
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                     (216 216
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                     (173 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                     (111 45 (:REWRITE DEFAULT-*-2))
                     (86 22 (:REWRITE DEFAULT-UNARY-MINUS))
                     (77 17 (:REWRITE DEFAULT-+-2))
                     (58 45 (:REWRITE DEFAULT-*-1))
                     (42 30 (:REWRITE DEFAULT-<-1))
                     (39 30 (:REWRITE DEFAULT-<-2))
                     (39 13 (:REWRITE FLOOR-WHEN-<))
                     (28 4
                         (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                     (25 17 (:REWRITE DEFAULT-+-1))
                     (24 24 (:TYPE-PRESCRIPTION MOD))
                     (13 13
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                     (13 13
                         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                     (13 13
                         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                     (13 13
                         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                     (13 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                     (12 12 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                     (12 12
                         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                     (12 12 (:LINEAR <-OF-*-AND-*))
                     (11 11
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                     (10 10 (:REWRITE DEFAULT-UNARY-/))
                     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                     (5 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
                     (5 1
                        (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
                     (4 4 (:REWRITE INTEGERP-OF-*))
                     (3 3 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
                     (3 1 (:DEFINITION NATP))
                     (2 1
                        (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
                     (1 1 (:TYPE-PRESCRIPTION NATP)))
(CEILING-LOWER-BOUND-LINEAR (3 1 (:REWRITE CEILING-WHEN-<=))
                            (2 2 (:REWRITE DEFAULT-<-2))
                            (2 2 (:REWRITE DEFAULT-<-1))
                            (1 1 (:REWRITE DEFAULT-UNARY-/))
                            (1 1 (:REWRITE DEFAULT-*-2))
                            (1 1 (:REWRITE DEFAULT-*-1)))
(<-OF-CEILING-ARG1 (844 844
                        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                   (844 844
                        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                   (346 196 (:REWRITE DEFAULT-*-2))
                   (337 39 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                   (268 136 (:REWRITE DEFAULT-<-2))
                   (226 196 (:REWRITE DEFAULT-*-1))
                   (203 51 (:REWRITE DEFAULT-UNARY-MINUS))
                   (187 78 (:LINEAR <-OF-*-AND-*))
                   (136 136 (:REWRITE DEFAULT-<-1))
                   (130 40 (:REWRITE DEFAULT-+-2))
                   (123 41 (:REWRITE FLOOR-WHEN-<))
                   (77 11
                       (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                   (76 40 (:REWRITE DEFAULT-+-1))
                   (66 66 (:TYPE-PRESCRIPTION MOD))
                   (43 43 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
                   (41 41
                       (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                   (41 41
                       (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                   (41 41
                       (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                   (41 41
                       (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                   (32 32
                       (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                   (27 8 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                   (26 4
                       (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
                   (25 25 (:REWRITE DEFAULT-UNARY-/))
                   (18 4 (:DEFINITION NATP))
                   (15 5 (:REWRITE <-OF-MINUS-AND-CONSTANT))
                   (11 11 (:REWRITE INTEGERP-OF-*))
                   (7 3 (:REWRITE <-OF-0-AND-FLOOR))
                   (4 4 (:TYPE-PRESCRIPTION NATP))
                   (2 2
                      (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR)))
(<-OF-CEILING-ARG2 (7 6 (:REWRITE DEFAULT-<-1))
                   (6 6 (:REWRITE DEFAULT-<-2))
                   (6 2 (:REWRITE CEILING-WHEN-<=))
                   (3 3 (:REWRITE DEFAULT-UNARY-/))
                   (3 3 (:REWRITE DEFAULT-*-2))
                   (3 3 (:REWRITE DEFAULT-*-1))
                   (3 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                   (2 2 (:REWRITE DEFAULT-+-2))
                   (2 2 (:REWRITE DEFAULT-+-1))
                   (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
                   (2 2
                      (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                   (2 2 (:LINEAR <-OF-*-AND-*))
                   (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                   (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                   (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                   (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1)))
(CEILING-OF-*-SAME (2 2 (:REWRITE DEFAULT-*-2))
                   (2 2 (:REWRITE DEFAULT-*-1))
                   (1 1 (:REWRITE DEFAULT-UNARY-/))
                   (1 1 (:REWRITE DEFAULT-<-2))
                   (1 1 (:REWRITE DEFAULT-<-1)))
(CEILING-WHEN-MULTIPLE
     (11 11 (:REWRITE DEFAULT-*-2))
     (11 11 (:REWRITE DEFAULT-*-1))
     (10 10 (:REWRITE DEFAULT-UNARY-/))
     (10 2 (:REWRITE DEFAULT-+-2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (6 2 (:REWRITE FLOOR-WHEN-<))
     (3 3 (:REWRITE INTEGERP-OF-*))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (2 2
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (2 2
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (2 2
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (2 2
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (2 2 (:REWRITE DEFAULT-+-1)))
(CEILING-OF-+-WHEN-MULTIPLE
     (61 61 (:REWRITE DEFAULT-*-2))
     (61 61 (:REWRITE DEFAULT-*-1))
     (55 23 (:REWRITE DEFAULT-+-2))
     (38 4 (:REWRITE CEILING-WHEN-MULTIPLE))
     (35 23 (:REWRITE DEFAULT-+-1))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (24 3 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
     (22 22 (:REWRITE DEFAULT-UNARY-/))
     (21 7 (:REWRITE FLOOR-WHEN-<))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (7 7
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (7 7
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (7 7
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (7 7
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (7 7 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (6 6 (:REWRITE INTEGERP-OF-*))
     (4 4
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
     (3 3
        (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT)))
(EQUAL-OF-0-AND-CEILING (16 1
                            (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                        (12 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                        (11 11 (:REWRITE DEFAULT-<-2))
                        (11 11 (:REWRITE DEFAULT-<-1))
                        (8 8
                           (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                        (8 8 (:LINEAR <-OF-*-AND-*))
                        (7 5 (:REWRITE DEFAULT-+-2))
                        (6 6 (:REWRITE DEFAULT-*-2))
                        (6 6 (:REWRITE DEFAULT-*-1))
                        (6 5 (:REWRITE DEFAULT-+-1))
                        (4 4 (:REWRITE INTEGERP-OF-*))
                        (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                        (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                        (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                        (3 3 (:REWRITE DEFAULT-UNARY-/))
                        (3 1 (:DEFINITION NFIX))
                        (2 1 (:REWRITE DENOMINATOR-WHEN-INTEGERP))
                        (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
                        (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                        (1 1 (:REWRITE DEFAULT-NUMERATOR))
                        (1 1 (:REWRITE DEFAULT-DENOMINATOR))
                        (1 1 (:DEFINITION IFIX)))
(<-OF-0-AND-CEILING)
(CEILING-MONOTONE
     (351 351
          (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (351 351
          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (351 351
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (69 49 (:REWRITE DEFAULT-<-2))
     (63 21 (:REWRITE FLOOR-WHEN-<))
     (61 49 (:REWRITE DEFAULT-<-1))
     (59 43 (:REWRITE DEFAULT-*-2))
     (47 43 (:REWRITE DEFAULT-*-1))
     (38 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (28 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (25 25 (:REWRITE DEFAULT-UNARY-/))
     (22 10 (:REWRITE DEFAULT-UNARY-MINUS))
     (22 6 (:REWRITE DEFAULT-+-2))
     (21 21
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (21 21
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (21 21
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (21 21
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (21 3
         (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (19 19
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (18 18 (:TYPE-PRESCRIPTION MOD))
     (18 6 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (14 6 (:REWRITE DEFAULT-+-1))
     (12 12
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (12 12 (:LINEAR <-OF-*-AND-*))
     (8 8 (:REWRITE INTEGERP-OF-*))
     (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (5 1
        (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (3 3 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (3 1 (:DEFINITION NATP))
     (2 2
        (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE <-OF-0-AND-FLOOR)))
(CEILING-UPPER-BOUND-WHEN-<-CONSTANT-LINEAR
     (52 4 (:REWRITE CEILING-WHEN-MULTIPLE))
     (27 27 (:REWRITE DEFAULT-*-2))
     (27 27 (:REWRITE DEFAULT-*-1))
     (26 2 (:REWRITE CEILING-OF-+-WHEN-MULTIPLE))
     (12 4 (:REWRITE CEILING-WHEN-<=))
     (9 9 (:REWRITE DEFAULT-UNARY-/))
     (8 8 (:REWRITE DEFAULT-+-2))
     (8 8 (:REWRITE DEFAULT-+-1))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 2 (:REWRITE INTEGERP-OF--))
     (2 2 (:REWRITE INTEGERP-OF-*))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
