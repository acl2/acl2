(SVL::STRLIST-TO-STR (31 1 (:DEFINITION SVL::STRLIST-TO-STR))
                     (28 1 (:DEFINITION STRING-APPEND))
                     (16 1 (:DEFINITION BINARY-APPEND))
                     (10 10
                         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                     (10 7 (:REWRITE DEFAULT-CDR))
                     (10 7 (:REWRITE DEFAULT-CAR))
                     (9 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                     (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
                     (5 2
                        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                     (3 2
                        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                     (1 1
                        (:REWRITE STR::COERCE-TO-STRING-REMOVAL)))
(SVL::SYM-APP-FNC)
(SVL::SA-BODY)
