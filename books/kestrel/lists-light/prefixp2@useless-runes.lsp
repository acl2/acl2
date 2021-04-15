(PREFIXP-OF-ADD-TO-END (850 305 (:REWRITE DEFAULT-CDR))
                       (637 33 (:DEFINITION NTHCDR))
                       (624 263 (:REWRITE DEFAULT-CAR))
                       (591 509 (:REWRITE DEFAULT-+-2))
                       (582 65 (:REWRITE PREFIXP-WHEN-LEN-0))
                       (549 387 (:REWRITE DEFAULT-<-2))
                       (510 509 (:REWRITE DEFAULT-+-1))
                       (454 387 (:REWRITE DEFAULT-<-1))
                       (362 362
                            (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                       (306 44 (:REWRITE EQUAL-OF-LEN-AND-0))
                       (141 141 (:REWRITE CONSP-WHEN-LEN-GREATER))
                       (51 51
                           (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
                       (24 24 (:REWRITE PREFIXP-OF-CDR-RULE))
                       (10 10
                           (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN)))
(PREFIXP-REWRITE (669 27 (:REWRITE PREFIXP-WHEN-NOT-SHORTER))
                 (576 28 (:REWRITE PREFIXP-WHEN-LONGER))
                 (552 125 (:REWRITE DEFAULT-CAR))
                 (376 109 (:REWRITE DEFAULT-CDR))
                 (342 199 (:REWRITE DEFAULT-<-2))
                 (277 191 (:REWRITE DEFAULT-+-2))
                 (270 199 (:REWRITE DEFAULT-<-1))
                 (194 194
                      (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                 (191 191 (:REWRITE DEFAULT-+-1))
                 (81 81 (:REWRITE CONSP-WHEN-LEN-GREATER))
                 (49 49
                     (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
                 (14 14
                     (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
                 (13 13 (:REWRITE PREFIXP-OF-CDR-RULE))
                 (10 10
                     (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN)))
(PREFIXP-REWRITE-GEN (438 131 (:REWRITE DEFAULT-CAR))
                     (376 17 (:REWRITE PREFIXP-WHEN-NOT-SHORTER))
                     (339 96 (:REWRITE DEFAULT-CDR))
                     (311 17 (:REWRITE PREFIXP-WHEN-LEN-0))
                     (288 41 (:REWRITE EQUAL-OF-LEN-AND-0))
                     (217 137 (:REWRITE DEFAULT-<-2))
                     (193 140 (:REWRITE DEFAULT-+-2))
                     (183 183
                          (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                     (172 137 (:REWRITE DEFAULT-<-1))
                     (140 140 (:REWRITE DEFAULT-+-1))
                     (104 16 (:REWRITE ZP-OPEN))
                     (52 52 (:REWRITE CONSP-WHEN-LEN-GREATER))
                     (41 41
                         (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
                     (13 13
                         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
                     (7 7 (:REWRITE PREFIXP-OF-CDR-RULE))
                     (5 5
                        (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN)))
