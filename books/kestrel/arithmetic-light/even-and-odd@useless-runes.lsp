(EVENP-OF-SUM-WHEN-EVENP-ARG1 (12 3 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                              (8 8 (:REWRITE DEFAULT-*-2))
                              (8 8 (:REWRITE DEFAULT-*-1))
                              (3 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                              (3 3
                                 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                              (3 3
                                 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                              (3 3 (:REWRITE INTEGERP-OF-*))
                              (2 2 (:REWRITE DEFAULT-+-2))
                              (2 2 (:REWRITE DEFAULT-+-1)))
(EVENP-OF-SUM-WHEN-EVENP-ARG2 (12 3 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                              (8 8 (:REWRITE DEFAULT-*-2))
                              (8 8 (:REWRITE DEFAULT-*-1))
                              (3 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                              (3 3
                                 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                              (3 3
                                 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                              (3 3 (:REWRITE INTEGERP-OF-*))
                              (3 3 (:REWRITE DEFAULT-+-2))
                              (3 3 (:REWRITE DEFAULT-+-1)))
(EVENP-REDUCE-ALT3 (14 3 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                   (13 12 (:REWRITE DEFAULT-*-2))
                   (12 12 (:REWRITE DEFAULT-*-1))
                   (9 8 (:REWRITE DEFAULT-+-2))
                   (9 8 (:REWRITE DEFAULT-+-1))
                   (9 2
                      (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
                   (7 2
                      (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
                   (3 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                   (3 3
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                   (3 3
                      (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                   (3 3
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                   (3 3 (:REWRITE INTEGERP-OF-*))
                   (3 3 (:REWRITE FOLD-CONSTS-IN-+))
                   (3 3 (:REWRITE +-COMBINE-CONSTANTS))
                   (1 1
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                   (1 1 (:TYPE-PRESCRIPTION MOD)))
(EVENP-OF-MINUS (12 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                (5 4 (:REWRITE DEFAULT-*-2))
                (5 4 (:REWRITE DEFAULT-*-1))
                (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                (2 2
                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                (2 2
                   (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                (2 2 (:TYPE-PRESCRIPTION MOD))
                (2 2
                   (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                (2 2
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                (2 2 (:REWRITE INTEGERP-OF-*))
                (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(EVENP-OF-ONE-MORE (6 6 (:REWRITE DEFAULT-*-2))
                   (6 6 (:REWRITE DEFAULT-*-1))
                   (4 1 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                   (2 2 (:REWRITE DEFAULT-+-2))
                   (2 2 (:REWRITE DEFAULT-+-1))
                   (1 1 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                   (1 1
                      (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                   (1 1
                      (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                   (1 1 (:REWRITE INTEGERP-OF-*)))
(ODD-PLUS-ODD-IS-EVEN (80 80 (:REWRITE DEFAULT-*-2))
                      (80 80 (:REWRITE DEFAULT-*-1))
                      (64 16 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                      (38 38 (:REWRITE DEFAULT-+-2))
                      (38 38 (:REWRITE DEFAULT-+-1))
                      (16 16
                          (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                      (16 16
                          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                      (16 16
                          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                      (16 16 (:REWRITE INTEGERP-OF-*))
                      (14 4
                          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
                      (14 4
                          (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
                      (12 12 (:REWRITE FOLD-CONSTS-IN-+)))
(EVENP-REDUCE-ODD-ALT (6 6 (:REWRITE DEFAULT-+-2))
                      (6 6 (:REWRITE DEFAULT-+-1))
                      (2 2
                         (:REWRITE EVENP-OF-SUM-WHEN-EVENP-ARG1)))
(EVENP-REDUCE-ODD (3 1 (:REWRITE ODD-PLUS-ODD-IS-EVEN))
                  (3 1
                     (:REWRITE EVENP-OF-SUM-WHEN-EVENP-ARG2))
                  (2 2 (:REWRITE DEFAULT-+-2))
                  (2 2 (:REWRITE DEFAULT-+-1))
                  (1 1
                     (:REWRITE EVENP-OF-SUM-WHEN-EVENP-ARG1)))
(EVENP-OF-PRODUCT-WHEN-EVENP (12 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
                             (8 6 (:REWRITE DEFAULT-*-1))
                             (7 6 (:REWRITE DEFAULT-*-2))
                             (3 3
                                (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                             (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
                             (2 2
                                (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
                             (2 2
                                (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
                             (2 2 (:TYPE-PRESCRIPTION MOD))
                             (2 2
                                (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
                             (2 2 (:REWRITE FOLD-CONSTS-IN-*))
                             (2 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
                             (1 1 (:REWRITE INTEGERP-OF-*)))
(EVENP-OF-PRODUCT-WHEN-EVENP-ALT
     (5 3 (:REWRITE DEFAULT-*-1))
     (4 3 (:REWRITE DEFAULT-*-2))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ODD-TIMES-ODD (32 8 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
               (28 28 (:REWRITE DEFAULT-*-2))
               (28 28 (:REWRITE DEFAULT-*-1))
               (8 8 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
               (8 8
                  (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
               (8 8
                  (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
               (5 5 (:REWRITE DEFAULT-+-2))
               (5 5 (:REWRITE DEFAULT-+-1))
               (5 1
                  (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-2))
               (5 1
                  (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
               (4 4 (:REWRITE FOLD-CONSTS-IN-*))
               (4 4 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
               (1 1
                  (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP)))
(ODD-OF-PRODUCT-WHEN-ODD (5 5 (:REWRITE DEFAULT-*-2))
                         (5 5 (:REWRITE DEFAULT-*-1)))
(EVENP-OF-PRODUCT-WHEN-ODD-ALT (13 13 (:REWRITE DEFAULT-*-2))
                               (13 13 (:REWRITE DEFAULT-*-1))
                               (12 4
                                   (:REWRITE EVENP-OF-PRODUCT-WHEN-EVENP)))
