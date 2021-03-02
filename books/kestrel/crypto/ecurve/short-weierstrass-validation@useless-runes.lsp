(ECURVE::RULE1)
(ECURVE::RULE2A)
(ECURVE::RULE2B)
(ECURVE::RULE3 (5 5 (:REWRITE DEFAULT-<-2))
               (5 5 (:REWRITE DEFAULT-<-1))
               (2 2 (:REWRITE DEFAULT-CDR))
               (2 2 (:REWRITE DEFAULT-CAR))
               (1 1
                  (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
               (1 1
                  (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
               (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(ECURVE::RULE4 (40 22
                   (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
               (40 22
                   (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
               (34 34 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
               (26 18
                   (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
               (24 24 (:REWRITE PFIELD::MUL-BECOMES-NEG))
               (22 12
                   (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
               (20 20
                   (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
               (18 18
                   (:TYPE-PRESCRIPTION PFIELD::NATP-OF-MUL))
               (18 18
                   (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
               (16 12
                   (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
               (14 14
                   (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
               (12 12
                   (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
               (12 12
                   (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS))
               (9 9 (:REWRITE DEFAULT-<-2))
               (9 9 (:REWRITE DEFAULT-<-1))
               (6 6
                  (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
               (4 4
                  (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
               (2 2 (:REWRITE DEFAULT-CDR))
               (2 2 (:REWRITE DEFAULT-CAR))
               (1 1 (:META CANCEL_IPLUS-EQUAL-CORRECT)))
(ECURVE::RULE5 (28 18
                   (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
               (26 26 (:REWRITE PFIELD::MUL-BECOMES-NEG))
               (25 13
                   (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
               (23 13
                   (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
               (22 22
                   (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
               (22 18
                   (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
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
               (2 2 (:REWRITE DEFAULT-CDR))
               (2 2 (:REWRITE DEFAULT-CAR))
               (2 2 (:REWRITE PFIELD::ADD-COMMUTATIVE-2))
               (2 2
                  (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS))
               (2 2 (:META CANCEL_IPLUS-EQUAL-CORRECT))
               (1 1 (:REWRITE ECURVE::RULE4)))
