(ECURVE::RULE1)
(ECURVE::RULE2A)
(ECURVE::RULE2B)
(ECURVE::RULE3 (7 7 (:META CANCEL_IPLUS-EQUAL-CORRECT))
               (5 5 (:REWRITE DEFAULT-CDR))
               (5 5 (:REWRITE DEFAULT-CAR))
               (5 5 (:REWRITE DEFAULT-<-2))
               (5 5 (:REWRITE DEFAULT-<-1))
               (1 1
                  (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
               (1 1
                  (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
               (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(ECURVE::RULE4 (160 88
                    (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
               (160 88
                    (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
               (136 136 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
               (104 72
                    (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
               (96 96 (:REWRITE PFIELD::MUL-BECOMES-NEG))
               (80 80
                   (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
               (72 72
                   (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
               (56 56
                   (:TYPE-PRESCRIPTION PFIELD::NATP-OF-MUL))
               (56 56
                   (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
               (48 48
                   (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
               (48 48
                   (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS))
               (24 24
                   (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
               (19 19 (:REWRITE DEFAULT-CAR))
               (16 16
                   (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
               (15 15 (:REWRITE DEFAULT-CDR))
               (10 10 (:META CANCEL_IPLUS-EQUAL-CORRECT))
               (9 9 (:REWRITE DEFAULT-<-2))
               (9 9 (:REWRITE DEFAULT-<-1)))
(ECURVE::RULE5 (26 26 (:REWRITE PFIELD::MUL-BECOMES-NEG))
               (25 13
                   (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
               (23 13
                   (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
               (22 22
                   (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
               (19 19 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
               (18 10
                   (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
               (8 8
                  (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
               (8 8
                  (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
               (6 6 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
               (6 6
                  (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
               (5 5 (:REWRITE DEFAULT-<-2))
               (5 5 (:REWRITE DEFAULT-<-1))
               (4 4 (:REWRITE DEFAULT-CDR))
               (4 4 (:REWRITE DEFAULT-CAR))
               (2 2 (:REWRITE PFIELD::ADD-COMMUTATIVE-2))
               (2 2
                  (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS))
               (2 2 (:META CANCEL_IPLUS-EQUAL-CORRECT))
               (1 1 (:REWRITE ECURVE::RULE4)))
