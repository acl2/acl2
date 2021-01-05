(WF-DAGP (145 145 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
         (2 2 (:LINEAR ARRAY2P-LINEAR))
         (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
         (1 1
            (:REWRITE BOUNDED-DAG-VARIABLE-ALISTP-MONOTONE))
         (1 1
            (:REWRITE BOUNDED-DAG-CONSTANT-ALISTP-MONOTONE)))
(WF-DAGP-EXPANDER (52 26 (:TYPE-PRESCRIPTION ALEN1-TYPE))
                  (26 26 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
                  (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
                  (2 2
                     (:REWRITE BOUNDED-DAG-VARIABLE-ALISTP-MONOTONE))
                  (2 2
                     (:REWRITE BOUNDED-DAG-CONSTANT-ALISTP-MONOTONE)))
(WF-DAGP-FORWARD (34 17 (:TYPE-PRESCRIPTION ALEN1-TYPE))
                 (17 17 (:TYPE-PRESCRIPTION POSP-OF-ALEN1)))
(WF-DAGP-FORWARD-TO-<=-OF-LEN (8 4 (:TYPE-PRESCRIPTION ALEN1-TYPE))
                              (4 4 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
                              (4 4 (:TYPE-PRESCRIPTION ARRAY1P)))
(WF-DAGP-OF-MAKE-EMPTY-ARRAY (2 2 (:REWRITE USE-ALL-<=-2))
                             (2 2 (:REWRITE USE-ALL-<=))
                             (2 2 (:REWRITE USE-ALL-<-2))
                             (2 2 (:REWRITE USE-ALL-<))
                             (2 2
                                (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
                             (2 2 (:REWRITE DEFAULT-<-2))
                             (2 2 (:REWRITE DEFAULT-<-1))
                             (2 2
                                (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
                             (1 1
                                (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN)))
