(INTEGERP-SQUEEZE)
(INTEGERP-OF-+-OF--1/2)
(INTEGERP-OF-- (3 2 (:REWRITE DEFAULT-UNARY-MINUS))
               (2 2
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(INTEGERP-OF-+-OF-1/2-AND-*-OF--1/2 (3 3 (:REWRITE DEFAULT-+-2))
                                    (3 3 (:REWRITE DEFAULT-+-1))
                                    (2 2 (:REWRITE DEFAULT-*-2))
                                    (2 2 (:REWRITE DEFAULT-*-1))
                                    (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(INTEGERP-OF-+-OF---AND-- (4 4
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
                          (3 2 (:REWRITE DEFAULT-+-2))
                          (3 2 (:REWRITE DEFAULT-+-1)))
(INTEGERP-OF-+-OF-1/2-AND-*-OF-1/2
     (74 9 (:REWRITE MOD-WHEN-MULTIPLE))
     (74 9
         (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (64 18 (:REWRITE COMMUTATIVITY-OF-*))
     (55 3 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (49 49
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (47 47 (:REWRITE DEFAULT-*-2))
     (47 47 (:REWRITE DEFAULT-*-1))
     (29 17 (:REWRITE DEFAULT-+-2))
     (24 8 (:REWRITE MOD-WHEN-<))
     (20 17 (:REWRITE DEFAULT-+-1))
     (15 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE DEFAULT-<-2))
     (9 9
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (9 9
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (9 9
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (9 9
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (9 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (8 8 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP)))
