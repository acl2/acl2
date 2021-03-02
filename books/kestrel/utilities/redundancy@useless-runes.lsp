(COMMAND-IS-REDUNDANTP (23 23 (:REWRITE DEFAULT-CAR))
                       (16 16 (:REWRITE DEFAULT-CDR))
                       (15 3 (:DEFINITION ASSOC-EQUAL))
                       (15 1 (:DEFINITION FGETPROP))
                       (6 2
                          (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
                       (4 2 (:DEFINITION NTH))
                       (4 1
                          (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
                       (3 1 (:DEFINITION ALISTP))
                       (2 2
                          (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
                       (2 1
                          (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL)))
