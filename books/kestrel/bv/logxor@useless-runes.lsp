(LOGXOR-COMMUTATIVE-NO-CLASH (4 2 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
                             (3 3
                                (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
                             (3 3
                                (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1))
                             (2 2 (:TYPE-PRESCRIPTION BINARY-LOGEQV)))
(LOGXOR-OF-0)
(LOGXOR-OF--1 (2 2 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
              (1 1
                 (:REWRITE EQUAL-OF-LOGNOT-AND-CONSTANT)))
(LOGXOR-WHEN-NOT-INTEGERP-ARG1 (2 1
                                  (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
                               (1 1 (:TYPE-PRESCRIPTION LOGNOT))
                               (1 1 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP)))
(LOGXOR-WHEN-NOT-INTEGERP-ARG2 (2 2
                                  (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
                               (2 2
                                  (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1)))
(LOGXOR-ASSOCIATIVE (16 10
                        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
                    (13 10
                        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1))
                    (3 3 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP)))
(MOD-OF-LOGXOR-AND-EXPT
     (104 17
          (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG2))
     (89 17
         (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG1))
     (60 14
         (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (46 8
         (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (45 14
         (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (44 8 (:REWRITE MOD-WHEN-<))
     (40 8 (:REWRITE MOD-WHEN-MULTIPLE))
     (26 6 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
     (24 8
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (24 8
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (22 22
         (:TYPE-PRESCRIPTION LOGAND-NEGATIVE-TYPE))
     (20 4 (:REWRITE DEFAULT-UNARY-/))
     (12 4 (:REWRITE DEFAULT-*-2))
     (11 4
         (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG2))
     (11 4
         (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG1))
     (10 4 (:REWRITE INTEGERP-OF-*))
     (8 8
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (8 8
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (8 8
        (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (8 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (7 3 (:REWRITE DEFAULT-<-2))
     (7 2
        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1))
     (6 6
        (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
     (6 2 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:LINEAR EXPT-BOUND-LINEAR))
     (4 2
        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
     (4 2 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (2 2 (:TYPE-PRESCRIPTION NATP-OF-EXPT)))
(LOGXOR-SAME)
(LOGXOR-COMMUTATIVE-2 (15 11
                          (:REWRITE LOGXOR-WHEN-NOT-INTEGERP-ARG2))
                      (13 11
                          (:REWRITE LOGXOR-WHEN-NOT-INTEGERP-ARG1)))
(LOGXOR-SAME-2)
(LOGXOR-COMBINE-CONSTANTS)
(FLOOR-OF-LOGXOR-BY-2 (76 15
                          (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG2))
                      (62 15
                          (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG1))
                      (53 53
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                      (53 53
                          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                      (47 12
                          (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG1-CHEAP))
                      (33 12
                          (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG2-CHEAP))
                      (22 6 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
                      (18 18
                          (:TYPE-PRESCRIPTION LOGAND-NON-NEGATIVE-TYPE))
                      (18 18
                          (:TYPE-PRESCRIPTION LOGAND-NEGATIVE-TYPE))
                      (10 6 (:REWRITE FLOOR-WHEN-<))
                      (10 4
                          (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG2))
                      (10 4
                          (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG1))
                      (6 6
                         (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
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
                      (6 2
                         (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1))
                      (4 2
                         (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
                      (2 2 (:REWRITE DEFAULT-<-2))
                      (2 2 (:REWRITE DEFAULT-<-1)))
(FLOOR-OF-LOGXOR-BY-2-BACK
     (25 25
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (25 25
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (11 3
         (:REWRITE LOGXOR-WHEN-NOT-INTEGERP-ARG2))
     (11 3
         (:REWRITE LOGXOR-WHEN-NOT-INTEGERP-ARG1))
     (8 4 (:REWRITE FLOOR-WHEN-<))
     (4 4
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (4 4
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (4 4
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (4 4
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (4 4
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (4 4 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(FLOOR-OF-LOGXOR-AND-EXPT
     (169 13 (:DEFINITION EXPT))
     (88 15
         (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG2))
     (72 15
         (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG1))
     (68 6 (:REWRITE FLOOR-WHEN-<))
     (57 57
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (57 57
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (53 12
         (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (41 12
         (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (39 13 (:REWRITE DEFAULT-*-2))
     (39 13 (:REWRITE COMMUTATIVITY-OF-+))
     (34 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (30 6 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
     (26 26 (:REWRITE DEFAULT-+-2))
     (26 26 (:REWRITE DEFAULT-+-1))
     (20 16 (:REWRITE DEFAULT-<-2))
     (18 18
         (:TYPE-PRESCRIPTION LOGAND-NON-NEGATIVE-TYPE))
     (18 18
         (:TYPE-PRESCRIPTION LOGAND-NEGATIVE-TYPE))
     (18 6
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (16 16 (:REWRITE DEFAULT-<-1))
     (13 13 (:REWRITE ZIP-OPEN))
     (13 13 (:REWRITE DEFAULT-*-1))
     (12 4
         (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG2))
     (12 4
         (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG1))
     (8 2
        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1))
     (6 6
        (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
     (6 6
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (6 6
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (6 6
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (6 6
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (6 6 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (4 4 (:LINEAR EXPT-BOUND-LINEAR))
     (4 2
        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
     (2 2 (:TYPE-PRESCRIPTION NATP-OF-EXPT)))
(LOGXOR-CANCEL (14 10
                   (:REWRITE LOGXOR-WHEN-NOT-INTEGERP-ARG2))
               (10 10
                   (:REWRITE LOGXOR-WHEN-NOT-INTEGERP-ARG1))
               (4 4 (:REWRITE LOGXOR-COMBINE-CONSTANTS)))
(LOGXOR-NON-NEGATIVE (105 1 (:REWRITE <-OF-LOGAND))
                     (54 3 (:DEFINITION NATP))
                     (35 13
                         (:TYPE-PRESCRIPTION LOGIOR-NON-NEGATIVE-TYPE))
                     (19 2 (:LINEAR LOGIOR-BOUND-LINEAR-2))
                     (19 2 (:LINEAR LOGIOR-BOUND-LINEAR))
                     (13 13 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
                     (13 13
                         (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
                     (11 9 (:REWRITE DEFAULT-<-1))
                     (9 9 (:TYPE-PRESCRIPTION NATP))
                     (9 9 (:REWRITE DEFAULT-<-2))
                     (6 1
                        (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG1-CHEAP))
                     (6 1 (:REWRITE LOGAND-OF-LOGIOR))
                     (4 3
                        (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG2))
                     (4 3
                        (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG1))
                     (4 1
                        (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG2-CHEAP))
                     (3 2
                        (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG2))
                     (3 2
                        (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG1))
                     (2 2
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (2 2 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
                     (2 1
                        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
                     (1 1
                        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1)))
(UNSIGNED-BYTE-P-OF-LOGXOR
     (23 7
         (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG2))
     (18 7
         (:REWRITE LOGIOR-WHEN-NOT-INTEGERP-ARG1))
     (16 5
         (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (10 6 (:REWRITE DEFAULT-<-2))
     (8 8 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (7 7
        (:TYPE-PRESCRIPTION LOGAND-NEGATIVE-TYPE))
     (7 5
        (:REWRITE LOGAND-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (6 6 (:REWRITE DEFAULT-<-1))
     (3 3
        (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
     (3 2
        (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG2))
     (3 2
        (:REWRITE LOGORC1-WHEN-NOT-INTEGERP-ARG1))
     (2 2 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
     (2 2 (:LINEAR EXPT-BOUND-LINEAR))
     (2 1
        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG2))
     (1 1
        (:REWRITE LOGEQV-WHEN-NOT-INTEGERP-ARG1)))
