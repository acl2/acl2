(ALL-INTEGERP-OF-REPEAT (25 5 (:REWRITE REPEAT-WHEN-ZP))
                        (17 7 (:REWRITE ZP-OPEN))
                        (10 5
                            (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
                        (5 5 (:TYPE-PRESCRIPTION REPEAT))
                        (4 4 (:REWRITE DEFAULT-<-2))
                        (4 4 (:REWRITE DEFAULT-<-1))
                        (2 2 (:REWRITE DEFAULT-+-2))
                        (2 2 (:REWRITE DEFAULT-+-1)))
