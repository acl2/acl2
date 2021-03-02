(LOGTAIL-OF-LOGIOR (1628 68 (:DEFINITION NATP))
                   (1008 55 (:LINEAR LOGIOR-BOUND-LINEAR-2))
                   (1008 55 (:LINEAR LOGIOR-BOUND-LINEAR))
                   (853 853
                        (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
                   (599 599
                        (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                   (599 599
                        (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                   (350 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
                   (333 216 (:REWRITE DEFAULT-<-1))
                   (292 10 (:REWRITE <-OF-FLOOR-AND-0))
                   (287 216 (:REWRITE DEFAULT-<-2))
                   (215 69
                        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                   (157 69
                        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                   (157 69
                        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                   (156 68
                        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                   (147 63 (:REWRITE DEFAULT-*-2))
                   (136 63 (:REWRITE DEFAULT-*-1))
                   (126 18 (:REWRITE NATP-OF-FLOOR))
                   (101 17 (:REWRITE DEFAULT-UNARY-/))
                   (76 20 (:REWRITE UNICITY-OF-1))
                   (69 69
                       (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                   (68 68 (:TYPE-PRESCRIPTION NATP))
                   (68 68 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                   (62 38 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
                   (56 20 (:DEFINITION FIX))
                   (50 10 (:REWRITE <-OF-FLOOR-AND-0-2))
                   (38 38 (:LINEAR EXPT-BOUND-LINEAR))
                   (34 18
                       (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
                   (18 3
                       (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
                   (14 14 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
                   (6 6 (:REWRITE <-OF-0-AND-EXPT))
                   (4 4
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(BVCHOP-OF-LOGIOR
     (1112 43 (:REWRITE MOD-WHEN-MULTIPLE))
     (904 43 (:REWRITE MOD-WHEN-<))
     (810 810
          (:TYPE-PRESCRIPTION <-OF-LOGIOR-AND-0-TYPE))
     (414 78 (:REWRITE DEFAULT-UNARY-/))
     (366 110 (:REWRITE DEFAULT-*-2))
     (280 110 (:REWRITE DEFAULT-*-1))
     (252 32 (:REWRITE COMMUTATIVITY-OF-*))
     (236 32 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (186 43
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (185 101 (:REWRITE DEFAULT-<-2))
     (157 101 (:REWRITE DEFAULT-<-1))
     (135 43
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (94 43
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (94 43
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (84 28 (:DEFINITION NATP))
     (74 74
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (42 13 (:REWRITE DEFAULT-+-2))
     (32 32 (:LINEAR EXPT-BOUND-LINEAR))
     (28 28 (:TYPE-PRESCRIPTION NATP))
     (14 14
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (14 14 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (13 13 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
