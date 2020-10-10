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
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (3 3 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
     (3 3 (:REWRITE EQUAL-OF---AND-CONSTANT))
     (3 2
        (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR)))
(CEILING-WHEN-<= (15 15 (:REWRITE DEFAULT-<-2))
                 (15 15 (:REWRITE DEFAULT-<-1))
                 (12 12 (:REWRITE DEFAULT-*-2))
                 (12 12 (:REWRITE DEFAULT-*-1))
                 (12 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                 (11 11 (:REWRITE DEFAULT-UNARY-/))
                 (10 10
                     (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                 (10 10
                     (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                 (10 10
                     (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                 (10 10
                     (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                 (8 8
                    (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
                 (8 8 (:LINEAR <-OF-*-AND-*))
                 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
                 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
                 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
                 (2 2 (:REWRITE INTEGERP-OF-*))
                 (2 2
                    (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1)))
(CEILING-OF-+-OF-MINUS-8 (102 48 (:REWRITE DEFAULT-+-2))
                         (84 84
                             (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                         (51 48 (:REWRITE DEFAULT-+-1))
                         (51 15 (:REWRITE DEFAULT-UNARY-MINUS))
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
        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (3 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (3 2 (:REWRITE DENOMINATOR-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 2 (:REWRITE <-OF-MINUS-AND-CONSTANT)))
(CEILING-UPPER-BOUND (381 381
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                     (218 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                     (216 7 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                     (112 16
                          (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                     (105 45 (:REWRITE DEFAULT-*-2))
                     (104 74 (:REWRITE DEFAULT-<-2))
                     (101 33 (:REWRITE FLOOR-WHEN-<))
                     (96 96 (:TYPE-PRESCRIPTION MOD))
                     (88 74 (:REWRITE DEFAULT-<-1))
                     (56 45 (:REWRITE DEFAULT-*-1))
                     (44 26 (:REWRITE DEFAULT-+-2))
                     (43 33
                         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                     (43 13 (:REWRITE DEFAULT-UNARY-MINUS))
                     (35 33
                         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                     (34 11 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                     (33 33
                         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                     (33 33
                         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                     (32 26 (:REWRITE DEFAULT-+-1))
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
(CEILING-LOWER-BOUND (223 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
                     (216 216
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                     (153 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                     (95 45 (:REWRITE DEFAULT-*-2))
                     (70 22 (:REWRITE DEFAULT-UNARY-MINUS))
                     (62 17 (:REWRITE DEFAULT-+-2))
                     (55 45 (:REWRITE DEFAULT-*-1))
                     (39 30 (:REWRITE DEFAULT-<-1))
                     (39 13 (:REWRITE FLOOR-WHEN-<))
                     (37 30 (:REWRITE DEFAULT-<-2))
                     (28 4
                         (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                     (24 24 (:TYPE-PRESCRIPTION MOD))
                     (23 17 (:REWRITE DEFAULT-+-1))
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
(<-OF-CEILING-ARG1 (854 854
                        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                   (316 199 (:REWRITE DEFAULT-*-2))
                   (287 39 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
                   (238 137 (:REWRITE DEFAULT-<-2))
                   (223 199 (:REWRITE DEFAULT-*-1))
                   (174 78 (:LINEAR <-OF-*-AND-*))
                   (165 51 (:REWRITE DEFAULT-UNARY-MINUS))
                   (137 137 (:REWRITE DEFAULT-<-1))
                   (126 42 (:REWRITE FLOOR-WHEN-<))
                   (110 41 (:REWRITE DEFAULT-+-2))
                   (77 11
                       (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
                   (68 41 (:REWRITE DEFAULT-+-1))
                   (66 66 (:TYPE-PRESCRIPTION MOD))
                   (43 43 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
                   (42 42
                       (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                   (42 42
                       (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                   (42 42
                       (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                   (42 42
                       (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                   (33 33
                       (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                   (28 28 (:REWRITE DEFAULT-UNARY-/))
                   (27 8 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
                   (26 4
                       (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
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
