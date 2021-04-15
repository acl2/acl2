(ALL-<=-ALL)
(ALL-<=-OF-CAR-OF-LAST (516 14 (:DEFINITION ALL-<=))
                       (287 18 (:REWRITE USE-ALL-<=-FOR-CAR))
                       (136 20 (:REWRITE ALL-<=-OF-CDR))
                       (77 18 (:REWRITE DEFAULT-<-1))
                       (70 49 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
                       (68 35
                           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (68 4 (:REWRITE USE-ALL-<=-FOR-CAR-OF-LAST))
                       (60 18 (:REWRITE DEFAULT-<-2))
                       (52 49
                           (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
                       (43 41 (:REWRITE DEFAULT-CDR))
                       (37 2 (:REWRITE ALL-<=-OF-LAST))
                       (34 27 (:REWRITE DEFAULT-CAR))
                       (22 18 (:REWRITE USE-ALL-<=))
                       (18 18 (:REWRITE USE-ALL-<=-2))
                       (18 18
                           (:REWRITE NOT-ALL-<=-WHEN-<-AND-MEMBER-EQUAL))
                       (4 4 (:TYPE-PRESCRIPTION MEMBERP)))
(ALL-<=-ALL-OF-APPEND (48 39 (:REWRITE DEFAULT-CAR))
                      (46 23
                          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                      (35 29 (:REWRITE DEFAULT-CDR))
                      (29 29
                          (:REWRITE NOT-ALL-<=-WHEN-<-AND-MEMBER-EQUAL))
                      (29 29
                          (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
                      (29 29 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
                      (24 4 (:REWRITE USE-ALL-<=-FOR-CAR))
                      (23 23 (:TYPE-PRESCRIPTION TRUE-LISTP))
                      (23 23 (:TYPE-PRESCRIPTION BINARY-APPEND))
                      (8 8
                         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                      (8 4 (:REWRITE DEFAULT-<-2))
                      (8 4 (:REWRITE DEFAULT-<-1))
                      (4 4 (:REWRITE USE-ALL-<=-2))
                      (4 4 (:REWRITE USE-ALL-<=)))
(ALL-<=-ALL-OF-REVERSE-LIST-ARG2
     (25 5 (:DEFINITION BINARY-APPEND))
     (24 24 (:REWRITE DEFAULT-CAR))
     (18 3 (:REWRITE USE-ALL-<=-FOR-CAR))
     (16 16 (:REWRITE DEFAULT-CDR))
     (15 15
         (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
     (15 15 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
     (14 14
         (:REWRITE NOT-ALL-<=-WHEN-<-AND-MEMBER-EQUAL))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 3 (:REWRITE DEFAULT-<-2))
     (6 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE USE-ALL-<=-2))
     (3 3 (:REWRITE USE-ALL-<=)))
(ALL-<=-ALL-OF-CDR-ARG1 (18 18
                            (:REWRITE NOT-ALL-<=-WHEN-<-AND-MEMBER-EQUAL))
                        (18 18 (:REWRITE DEFAULT-CAR))
                        (18 18
                            (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
                        (18 14 (:REWRITE ALL-<=-WHEN-NOT-CONSP)))
(ALL-<=-ALL-WHEN-NOT-CONSP-ARG1-CHEAP
     (4 4
        (:REWRITE NOT-ALL-<=-WHEN-<-AND-MEMBER-EQUAL))
     (4 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE ALL-<=-MONOTONE))
     (2 2 (:REWRITE DEFAULT-CDR)))
