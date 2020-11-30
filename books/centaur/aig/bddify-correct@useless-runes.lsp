(UBDDP-VAL-ALISTP)
(UBDDP-VAL-ALISTP-HONS-ASSOC-EQUAL
     (57 22 (:REWRITE DEFAULT-CDR))
     (50 50
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (40 40 (:REWRITE DEFAULT-CAR))
     (20 10
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (12 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP)))
(UBDDP-AIG-Q-COMPOSE (108 9 (:DEFINITION UBDDP-VAL-ALISTP))
                     (75 5 (:DEFINITION HONS-ASSOC-EQUAL))
                     (62 62
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (54 54 (:REWRITE DEFAULT-CDR))
                     (45 45 (:REWRITE DEFAULT-CAR))
                     (28 14
                         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                     (18 3 (:DEFINITION Q-NOT))
                     (17 9 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                     (10 5 (:DEFINITION HONS-EQUAL))
                     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
                     (3 3 (:DEFINITION HONS)))
(SUBALISTP)
(BDD-EQUIV)
(BDD-EQUIV-NECC)
(BDD-EQUIV-REFL (2 2
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                (2 2
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                (2 2
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                (2 2
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                (2 2
                   (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-SYMM (4 4
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                (4 4
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                (4 4
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                (4 4
                   (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                (4 4
                   (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-TRANS (6 6
                    (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                 (6 6
                    (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                 (6 6
                    (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                 (6 6
                    (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                 (6 6
                    (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-IS-AN-EQUIVALENCE)
(BDD-EQUIV-IMPLIES-EQUAL-EVAL-BDD-1)
(BDD-IMPL)
(BDD-IMPL-NECC)
(BDDS-EQUAL-INSTANCE-RULE-CORRECT)
(BDDS-BDD-EQUIV-INSTANCE-RULE-CORRECT)
(NOT-BDD-INSTANCE-RULE-CORRECT)
(BDDS-SUBSET-INSTANCE-RULE-CORRECT)
(BDD-EQUIV-WITNESSING-WITNESS-RULE-CORRECT
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (4 4
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-IMPL-WITNESSING-WITNESS-RULE-CORRECT
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (4 4
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (2 2 (:REWRITE BDD-IMPL-NECC)))
(BDD-EQUIV-IMPLIES-EQUAL-BDD-IMPL-1
     (15 15 (:REWRITE BDD-IMPL-NECC))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (8 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-IMPLIES-EQUAL-BDD-IMPL-2
     (15 15 (:REWRITE BDD-IMPL-NECC))
     (11 11
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 9
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-IMPLIES-BDD-EQUIV-Q-AND-1
     (12 8
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:TYPE-PRESCRIPTION QS-SUBSET)))
(BDD-EQUIV-IMPLIES-BDD-EQUIV-Q-AND-2
     (12 8
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:TYPE-PRESCRIPTION QS-SUBSET)))
(BDD-EQUIV-IMPLIES-BDD-EQUIV-Q-NOT-1
     (36 6 (:DEFINITION Q-NOT))
     (12 12
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE DEFAULT-CAR))
     (6 6 (:DEFINITION HONS))
     (4 4
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-IMPL-SELF (2 2 (:REWRITE BDD-IMPL-NECC)))
(BDD-IMPL-NIL-IS-BDD-EQUIV-NIL (6 6 (:REWRITE BDD-IMPL-NECC))
                               (1 1
                                  (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                               (1 1
                                  (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                               (1 1
                                  (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                               (1 1
                                  (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-IMPL-T-IS-BDD-EQUIV-T (6 6 (:REWRITE BDD-IMPL-NECC))
                           (3 3
                              (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                           (3 3
                              (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                           (1 1
                              (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                           (1 1
                              (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(AIG-Q-COMPOSE-NIL)
(BDD-IMPL-TRANSITIVE-1 (6 6 (:REWRITE BDD-IMPL-NECC)))
(BDD-IMPL-TRANSITIVE-2 (2 2 (:REWRITE BDD-IMPL-NECC)))
(SUBALISTP-HONS-ASSOC-EQUAL
     (170 170 (:REWRITE DEFAULT-CAR))
     (138 138
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (74 37
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (54 54 (:REWRITE DEFAULT-CDR)))
(UBDDP-VAL-ALISTP-SUBALISTP
     (106 106
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (99 99 (:REWRITE DEFAULT-CAR))
     (65 60 (:REWRITE DEFAULT-CDR))
     (54 27
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (8 8
        (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(MERGE-HI-LO-BOUNDS-0-B (101 101
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                        (89 89
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                        (80 80
                            (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                        (26 26 (:TYPE-PRESCRIPTION UBDDP))
                        (18 6
                            (:REWRITE |(qs-subset x (q-and x y))|))
                        (16 16
                            (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (16 8 (:REWRITE DEFAULT-*-2))
                        (16 8 (:REWRITE DEFAULT-*-1))
                        (15 5
                            (:REWRITE |(qs-subset y (q-and x y))|))
                        (6 2
                           (:REWRITE |(qs-subset (q-and x y) x)|)))
(MERGE-HI-LO-BOUNDS-1-B (66 66
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                        (64 64
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                        (58 58
                            (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                        (16 16
                            (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (16 8 (:REWRITE DEFAULT-*-2))
                        (16 8 (:REWRITE DEFAULT-*-1))
                        (14 14 (:TYPE-PRESCRIPTION UBDDP))
                        (12 4
                            (:REWRITE |(qs-subset (q-and x y) x)|))
                        (6 2
                           (:REWRITE |(qs-subset (q-and x y) y)|))
                        (3 1
                           (:REWRITE |(qs-subset x (q-and x y))|)))
(MERGE-HI-LO-AIG-Q-COMPOSE
     (3090 206 (:DEFINITION HONS-ASSOC-EQUAL))
     (2293 93 (:DEFINITION BDD-EVAL-ALST))
     (1630 1630 (:TYPE-PRESCRIPTION QS-SUBSET))
     (1515 1000 (:REWRITE DEFAULT-CDR))
     (1402 1402 (:REWRITE DEFAULT-CAR))
     (1402 1402
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (1289 413
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (1167 413
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (824 206
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (598 299
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (595 389
          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (515 103
          (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (413 413
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (413 413
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (309 309
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (299 299 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (206 206 (:TYPE-PRESCRIPTION BDD-EVAL-ALST))
     (206 206
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (206 206
          (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (36 36
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (36 18 (:REWRITE DEFAULT-*-2))
     (36 18 (:REWRITE DEFAULT-*-1)))
(UBDDP-MERGE-HI-LO (8 8
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                   (8 4 (:REWRITE DEFAULT-*-2))
                   (8 4 (:REWRITE DEFAULT-*-1)))
(PRUNE-BY-COUNT-NIL-IMPL (11 5
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                         (10 5 (:REWRITE DEFAULT-<-1))
                         (8 8
                            (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                         (8 5 (:REWRITE DEFAULT-<-2))
                         (5 5
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                         (5 5
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                         (5 5
                            (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                         (2 2 (:REWRITE DEFAULT-+-2))
                         (2 2 (:REWRITE DEFAULT-+-1)))
(PRUNE-BY-COUNT-T-IMPL (13 7
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                       (10 5 (:REWRITE DEFAULT-<-1))
                       (8 8
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (8 5 (:REWRITE DEFAULT-<-2))
                       (7 7
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                       (6 6
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                       (6 6
                          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                       (2 2 (:REWRITE DEFAULT-+-2))
                       (2 2 (:REWRITE DEFAULT-+-1)))
(UBDDP-PRUNE-BY-COUNT (4 2 (:REWRITE DEFAULT-<-1))
                      (3 3
                         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                      (3 2 (:REWRITE DEFAULT-<-2))
                      (1 1 (:REWRITE DEFAULT-+-2))
                      (1 1 (:REWRITE DEFAULT-+-1)))
(UBDDP-AND-BDDIFY-X-WEAKENING)
(AND-BDDIFY-X-WEAKENING-BOUNDS
     (8820 588 (:DEFINITION HONS-ASSOC-EQUAL))
     (7113 281 (:DEFINITION BDD-EVAL-ALST))
     (4371 2901 (:REWRITE DEFAULT-CDR))
     (4064 4064 (:REWRITE DEFAULT-CAR))
     (4064 4064
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (2352 588
           (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (1866 1278
           (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (1738 869
           (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1499 1499
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (1489 1489
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (1470 294
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (882 882
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (869 869 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (588 588 (:TYPE-PRESCRIPTION BDD-EVAL-ALST))
     (588 588
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (588 588
          (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (588 588 (:DEFINITION HONS-EQUAL))
     (172 172 (:TYPE-PRESCRIPTION UBDDP))
     (75 25
         (:REWRITE |(qs-subset (q-and x y) y)|))
     (75 25
         (:REWRITE |(qs-subset (q-and x y) x)|))
     (54 18
         (:REWRITE |(qs-subset y (q-and x y))|))
     (54 18
         (:REWRITE |(qs-subset x (q-and x y))|)))
(AND-BDDIFY-X-WEAKENING-IMPL
     (5340 356 (:DEFINITION HONS-ASSOC-EQUAL))
     (4284 176 (:DEFINITION BDD-EVAL-ALST))
     (2664 1774 (:REWRITE DEFAULT-CDR))
     (2484 2484 (:REWRITE DEFAULT-CAR))
     (2484 2484
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (1424 356
           (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (1105 749
           (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (1064 532
           (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1046 1046
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (964 964
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (890 178
          (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (534 534
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (532 532 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (356 356 (:TYPE-PRESCRIPTION BDD-EVAL-ALST))
     (356 356
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (356 356
          (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (356 356 (:DEFINITION HONS-EQUAL))
     (344 344 (:TYPE-PRESCRIPTION UBDDP))
     (138 46
          (:REWRITE |(qs-subset y (q-and x y))|))
     (138 46
          (:REWRITE |(qs-subset x (q-and x y))|))
     (120 40
          (:REWRITE |(qs-subset (q-and x y) y)|))
     (120 40
          (:REWRITE |(qs-subset (q-and x y) x)|))
     (116 116 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (116 116 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (116 116 (:REWRITE BDD-IMPL-NECC)))
(AND-BDDIFY-X-WEAKENING-Q-COMPOSE
     (8190 546 (:DEFINITION HONS-ASSOC-EQUAL))
     (7721 315 (:DEFINITION BDD-EVAL-ALST))
     (4221 2856 (:REWRITE DEFAULT-CDR))
     (3990 3990 (:REWRITE DEFAULT-CAR))
     (3990 3990
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (2184 546
           (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (1722 861
           (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1705 1159
           (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (1365 273
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (1339 1339
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (1319 1319
           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (861 861 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (819 819
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (546 546 (:TYPE-PRESCRIPTION BDD-EVAL-ALST))
     (546 546
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (546 546
          (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (546 546 (:DEFINITION HONS-EQUAL))
     (68 68 (:TYPE-PRESCRIPTION UBDDP))
     (30 10
         (:REWRITE |(qs-subset y (q-and x y))|))
     (30 10
         (:REWRITE |(qs-subset x (q-and x y))|))
     (21 7
         (:REWRITE |(qs-subset (q-and x y) y)|))
     (21 7
         (:REWRITE |(qs-subset (q-and x y) x)|)))
(AND-BDDIFY-X-WEAKENING-EQUIV
     (1680 112 (:DEFINITION HONS-ASSOC-EQUAL))
     (1497 63 (:DEFINITION BDD-EVAL-ALST))
     (861 581 (:REWRITE DEFAULT-CDR))
     (842 842 (:TYPE-PRESCRIPTION QS-SUBSET))
     (812 812 (:REWRITE DEFAULT-CAR))
     (812 812
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (692 262
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (674 262
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (448 112
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (350 175
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (305 193
          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (280 56 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (262 262
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (262 262
          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (175 175 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (168 168
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (112 112 (:TYPE-PRESCRIPTION BDD-EVAL-ALST))
     (112 112
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (112 112
          (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (112 112 (:DEFINITION HONS-EQUAL))
     (8 8 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (8 8 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (8 8 (:REWRITE BDD-IMPL-NECC)))
(ABS-FMEMO-OKP)
(ABS-FMEMO-WFP)
(ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1
     (151 135 (:REWRITE DEFAULT-CAR))
     (90 90
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (68 58 (:REWRITE DEFAULT-CDR))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (10 10
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW2
     (151 135 (:REWRITE DEFAULT-CAR))
     (100 100
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (90 64 (:REWRITE DEFAULT-CDR))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (10 10
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-UBDDP
     (100 84 (:REWRITE DEFAULT-CAR))
     (76 76
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (40 30 (:REWRITE DEFAULT-CDR))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (10 10
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(APQS-MEMO-OKP)
(APQS-MEMO-WFP)
(APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL
     (355 299 (:REWRITE DEFAULT-CAR))
     (236 198 (:REWRITE DEFAULT-CDR))
     (204 204
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (65 42 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (42 21
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (30 30 (:REWRITE BDD-IMPL-NECC))
     (19 19
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (6 6
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1)))
(APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL-TRANS-1
     (3 1 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (2 2
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (2 2 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE BDD-IMPL-NECC))
     (1 1
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1)))
(APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL-TRANS-2
     (60 1 (:DEFINITION APQS-MEMO-OKP))
     (33 29 (:REWRITE DEFAULT-CAR))
     (28 2 (:DEFINITION HONS-ASSOC-EQUAL))
     (24 24
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (24 22 (:REWRITE DEFAULT-CDR))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (3 3 (:REWRITE BDD-IMPL-NECC))
     (3 3 (:DEFINITION HONS-EQUAL))
     (2 2
        (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(APQS-MEMO-OKP-HONS-ASSOC-EQUAL-AIG-Q-COMPOSE-EQUAL
     (228 198 (:REWRITE DEFAULT-CAR))
     (175 133 (:REWRITE DEFAULT-CDR))
     (138 138
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (14 14 (:REWRITE BDD-IMPL-NECC))
     (10 10
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(APQS-MEMO-OKP-HONS-ASSOC-EQUAL-UBDDP
     (237 179 (:REWRITE DEFAULT-CAR))
     (178 178
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (144 106 (:REWRITE DEFAULT-CDR))
     (102 6
          (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-UBDDP))
     (84 6 (:DEFINITION ABS-FMEMO-WFP))
     (42 21
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (30 30 (:TYPE-PRESCRIPTION ABS-FMEMO-WFP))
     (19 19
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL)))
(APQS-MEMO-OKP-CONSP-CDR-HONS-ASSOC-EQUAL
     (314 294 (:REWRITE DEFAULT-CAR))
     (255 217 (:REWRITE DEFAULT-CDR))
     (210 210
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (44 22
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (22 22
         (:REWRITE SUBALISTP-HONS-ASSOC-EQUAL))
     (20 20 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (20 20 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (20 20 (:REWRITE BDD-IMPL-NECC)))
(APQS-MEMO-LOOKUP-OK (368 16 (:DEFINITION AIG-Q-COMPOSE))
                     (128 32 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                     (121 99 (:REWRITE DEFAULT-CDR))
                     (96 16 (:DEFINITION Q-NOT))
                     (87 61 (:REWRITE DEFAULT-CAR))
                     (80 16 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                     (64 16 (:DEFINITION AIG-ALIST-LOOKUP))
                     (56 56
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (48 48
                         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                     (32 32
                         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                     (24 20
                         (:REWRITE APQS-MEMO-OKP-CONSP-CDR-HONS-ASSOC-EQUAL))
                     (16 16 (:DEFINITION HONS))
                     (8 8 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                     (3 3 (:REWRITE BDD-IMPL-NECC))
                     (3 1
                        (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL)))
(APQS-MEMO-LOOKUP-UBDDP
     (671 167 (:REWRITE DEFAULT-CAR))
     (612 20
          (:REWRITE APQS-MEMO-OKP-CONSP-CDR-HONS-ASSOC-EQUAL))
     (584 4 (:DEFINITION APQS-MEMO-OKP))
     (368 16 (:DEFINITION AIG-Q-COMPOSE))
     (216 182 (:REWRITE DEFAULT-CDR))
     (128 128
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (128 32 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (96 16 (:DEFINITION Q-NOT))
     (80 16 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (65 3 (:DEFINITION APQS-MEMO-WFP))
     (64 16 (:DEFINITION AIG-ALIST-LOOKUP))
     (48 48
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (32 32
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (32 2 (:DEFINITION ABS-FMEMO-WFP))
     (20 20 (:TYPE-PRESCRIPTION APQS-MEMO-OKP))
     (16 16 (:TYPE-PRESCRIPTION BDD-IMPL))
     (16 16 (:DEFINITION HONS))
     (8 8 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (8 8 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (8 4
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (4 4 (:TYPE-PRESCRIPTION BDD-EQUIV))
     (4 4 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (4 4 (:DEFINITION HONS-EQUAL)))
(APQS-MEMO-CACHE-OK (1304 326
                          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                    (1102 1032 (:REWRITE DEFAULT-CDR))
                    (1035 1007 (:REWRITE DEFAULT-CAR))
                    (894 149 (:DEFINITION Q-NOT))
                    (815 163
                         (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                    (654 654
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                    (489 489
                         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                    (326 326
                         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                    (278 14 (:DEFINITION BDD-EVAL-ALST))
                    (149 149 (:DEFINITION HONS))
                    (82 41
                        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                    (74 46
                        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                    (67 52 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                    (52 52
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                    (50 50
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                    (44 44 (:REWRITE BDD-IMPL-NECC))
                    (41 41 (:TYPE-PRESCRIPTION ATOM-LISTP)))
(APQS-MEMO-CACHE-WFP (86 74 (:REWRITE DEFAULT-CAR))
                     (78 78
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (59 59 (:REWRITE DEFAULT-CDR))
                     (22 11
                         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                     (11 11 (:TYPE-PRESCRIPTION ATOM-LISTP)))
(AIG-BDDIFY-X-WEAKENING-OK-UBDDP
     (552 552
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (446 378 (:REWRITE DEFAULT-CAR))
     (348 348 (:REWRITE DEFAULT-CDR))
     (172 86
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (12 2 (:DEFINITION Q-NOT))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (2 2 (:DEFINITION HONS)))
(AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV
     (84 21 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (51 11 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (37 37 (:REWRITE DEFAULT-CDR))
     (36 6 (:DEFINITION Q-NOT))
     (32 32
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (28 28 (:REWRITE DEFAULT-CAR))
     (16 16
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (6 6 (:DEFINITION HONS))
     (6 2 (:REWRITE Q-NOT-UNDER-IFF)))
(AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV
     (30 5 (:DEFINITION Q-NOT))
     (28 7 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (21 3
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (14 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (13 13 (:REWRITE DEFAULT-CDR))
     (12 12 (:REWRITE DEFAULT-CAR))
     (10 10
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (9 9 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (8 2 (:DEFINITION AIG-ALIST-LOOKUP))
     (5 5 (:DEFINITION HONS))
     (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (2 2 (:DEFINITION HONS-GET)))
(AIG-Q-COMPOSE-OF-AIG-NOT
     (110 6 (:DEFINITION AIG-Q-COMPOSE))
     (78 2 (:DEFINITION AIG-EVAL))
     (68 20 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (54 9 (:DEFINITION Q-NOT))
     (49 39 (:REWRITE DEFAULT-CDR))
     (48 2 (:DEFINITION AIG-ENV-LOOKUP))
     (40 4
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (38 2 (:DEFINITION BDD-EVAL-ALST))
     (36 8 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (33 33 (:REWRITE DEFAULT-CAR))
     (30 30
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (28 28
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (26 2
         (:REWRITE HONS-ASSOC-EQUAL-COMMUTES-BDD-EVAL-ALIST-TO-EVAL-BDD))
     (24 6 (:DEFINITION AIG-ALIST-LOOKUP))
     (20 20
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (18 18
         (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (16 4
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (10 6
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 9 (:DEFINITION HONS))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (8 8 (:DEFINITION HONS-GET))
     (4 2
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (2 2 (:TYPE-PRESCRIPTION ATOM-LISTP)))
(AIG-Q-COMPOSE-OF-VAR (8 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                      (3 3
                         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                      (2 2 (:REWRITE DEFAULT-CDR)))
(AIG-Q-COMPOSE-OF-CONST (4 1 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
                        (2 2 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                        (1 1 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P)))
(BDD-IMPL-OF-Q-NOT (108 18 (:DEFINITION Q-NOT))
                   (36 36
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                   (19 16 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                   (18 18 (:REWRITE DEFAULT-CDR))
                   (18 18 (:REWRITE DEFAULT-CAR))
                   (18 18 (:DEFINITION HONS))
                   (14 14 (:REWRITE BDD-IMPL-NECC))
                   (12 12
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                   (10 10
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                   (5 5
                      (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-OF-Q-NOT (48 8 (:DEFINITION Q-NOT))
                    (16 16
                        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                    (8 8 (:REWRITE DEFAULT-CDR))
                    (8 8 (:REWRITE DEFAULT-CAR))
                    (8 8 (:DEFINITION HONS))
                    (6 6
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                    (6 6
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                    (6 6
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                    (6 6
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                    (4 4
                       (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-IMPL-T (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-2))
            (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-1))
            (4 4 (:REWRITE BDD-IMPL-NECC))
            (2 2
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
            (2 2
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
            (1 1
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
            (1 1
               (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-IMPL-NIL (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-2))
              (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-1))
              (4 4 (:REWRITE BDD-IMPL-NECC))
              (1 1
                 (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
              (1 1
                 (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
              (1 1
                 (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
              (1 1
                 (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1)))
(BDD-IMPL-OF-AND-BDDIFY-X-WEAKENING-1
     (294 6 (:DEFINITION AIG-Q-COMPOSE))
     (192 24 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (126 30 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (84 84
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (84 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (72 72
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (72 24 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (48 48 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 6
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (36 6 (:DEFINITION Q-NOT))
     (24 24 (:REWRITE DEFAULT-CDR))
     (24 6
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (24 6 (:DEFINITION AIG-ALIST-LOOKUP))
     (18 18 (:REWRITE DEFAULT-CAR))
     (12 12
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (6 6 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (6 6 (:DEFINITION HONS-GET))
     (6 6 (:DEFINITION HONS))
     (5 5 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (5 5 (:REWRITE BDD-IMPL-NECC)))
(BDD-EQUIV-NIL-OF-AND-BDDIFY-X-WEAKENING-1)
(BDD-IMPL-OF-AND-BDDIFY-X-WEAKENING-0
     (294 6 (:DEFINITION AIG-Q-COMPOSE))
     (192 24 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (126 30 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (84 84
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (84 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (72 72
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (72 24 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (48 48 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 6
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (36 6 (:DEFINITION Q-NOT))
     (24 24 (:REWRITE DEFAULT-CDR))
     (24 6
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (24 6 (:DEFINITION AIG-ALIST-LOOKUP))
     (18 18 (:REWRITE DEFAULT-CAR))
     (12 12
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (6 6 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (6 6 (:DEFINITION HONS-GET))
     (6 6 (:DEFINITION HONS))
     (5 5 (:REWRITE BDD-IMPL-NECC)))
(BDD-EQUIV-T-OF-AND-BDDIFY-X-WEAKENING-1)
(AIG-BDDIFY-X-WEAKENING-OK
     (2260 2138 (:REWRITE DEFAULT-CAR))
     (1542 1542 (:REWRITE DEFAULT-CDR))
     (1238 1238
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (634 338 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (244 122
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (168 168 (:REWRITE BDD-IMPL-NECC))
     (94 2
         (:REWRITE BDD-EQUIV-T-OF-AND-BDDIFY-X-WEAKENING-1))
     (94 2
         (:REWRITE BDD-EQUIV-NIL-OF-AND-BDDIFY-X-WEAKENING-1))
     (54 9 (:DEFINITION Q-NOT))
     (9 9 (:DEFINITION HONS))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1)))
(BDD-EQUIV-LIST (66 31 (:REWRITE DEFAULT-+-2))
                (40 31 (:REWRITE DEFAULT-+-1))
                (24 24
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                (22 22 (:REWRITE DEFAULT-CDR))
                (6 2 (:REWRITE DEFAULT-<-2))
                (6 2 (:REWRITE DEFAULT-<-1))
                (4 4 (:REWRITE DEFAULT-CAR)))
(BDD-EQUIV-WHEN-BOTH-IMPLICATIONS (7 7
                                     (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                                  (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                                  (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                                  (6 6 (:REWRITE BDD-IMPL-NECC))
                                  (4 4
                                     (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                                  (4 4
                                     (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(BDD-EQUIV-LIST-REFL (6 6 (:REWRITE DEFAULT-CDR))
                     (6 6
                        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (4 4 (:REWRITE DEFAULT-CAR))
                     (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                     (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(BDD-EQUIV-LIST-IS-AN-EQUIVALENCE
     (144 144
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (116 116 (:REWRITE DEFAULT-CAR))
     (72 72 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (72 72 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (20 20 (:REWRITE DEFAULT-CDR)))
(AIG-BDDIFY-LIST-X-WEAKENING-OK
     (4960 620 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (3255 775
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (2170 2170
           (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (2116 1031
           (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (1860 620 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (1752 1752
           (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (1240 1240 (:TYPE-PRESCRIPTION BOOLEANP))
     (1166 1125 (:REWRITE DEFAULT-CAR))
     (1104 1097 (:REWRITE DEFAULT-CDR))
     (930 155 (:DEFINITION Q-NOT))
     (896 128
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (760 760
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (512 128
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (155 155 (:DEFINITION HONS))
     (150 132 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (68 34
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (40 40 (:REWRITE BDD-IMPL-NECC)))
(BDD-MAX-DEPTH (714 238 (:REWRITE UBDD-FIX-X-IS-X))
               (628 304 (:REWRITE DEFAULT-+-2))
               (476 476 (:TYPE-PRESCRIPTION UBDDP))
               (418 304 (:REWRITE DEFAULT-+-1))
               (302 302
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
               (300 30 (:DEFINITION LENGTH))
               (253 249 (:REWRITE DEFAULT-CAR))
               (251 247 (:REWRITE DEFAULT-CDR))
               (240 60 (:DEFINITION INTEGER-ABS))
               (210 30 (:DEFINITION LEN))
               (108 80 (:REWRITE DEFAULT-<-2))
               (97 80 (:REWRITE DEFAULT-<-1))
               (82 82 (:REWRITE FOLD-CONSTS-IN-+))
               (66 6 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
               (64 32
                   (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
               (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
               (30 30 (:TYPE-PRESCRIPTION LEN))
               (30 30 (:REWRITE DEFAULT-REALPART))
               (30 30 (:REWRITE DEFAULT-NUMERATOR))
               (30 30 (:REWRITE DEFAULT-IMAGPART))
               (30 30 (:REWRITE DEFAULT-DENOMINATOR))
               (30 30 (:REWRITE DEFAULT-COERCE-2))
               (30 30 (:REWRITE DEFAULT-COERCE-1))
               (28 4 (:DEFINITION MEMBER-EQUAL))
               (20 20 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
               (14 14 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
               (10 10 (:REWRITE SUBSETP-MEMBER . 2))
               (10 10 (:REWRITE SUBSETP-MEMBER . 1))
               (10 2 (:REWRITE SUBSETP-CAR-MEMBER))
               (2 2 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
               (2 2 (:REWRITE SUBSETP-TRANS2))
               (2 2 (:REWRITE SUBSETP-TRANS))
               (2 2 (:REWRITE SUBSETP-REFL))
               (2 2 (:REWRITE MEMBER-SELF))
               (2 2 (:REWRITE MEMBER-OF-CAR)))
(BDD-AL-MAX-DEPTH)
(BDD-AL-MAX-DEPTH-HONS-ASSOC-EQUAL
     (71 29 (:REWRITE DEFAULT-<-2))
     (56 56
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (55 29 (:REWRITE DEFAULT-<-1))
     (45 45 (:REWRITE DEFAULT-CAR))
     (24 12
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (18 18
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(BDD-EQUIV-OF-UBDD-FIX (5 1
                          (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
                       (3 3
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                       (3 3
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                       (3 3
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                       (3 3
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                       (3 1 (:REWRITE UBDD-FIX-X-IS-X))
                       (2 2 (:TYPE-PRESCRIPTION UBDDP))
                       (2 2
                          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                       (1 1 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                       (1 1 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(BDD-EQUIV-IMPLIES-EQUAL-UBDD-FIX-1
     (10 6 (:REWRITE UBDD-FIX-X-IS-X))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (2 2
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(NOT-CONSP-UBDD-FIX (126 28
                         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
                    (28 7 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
                    (28 7
                        (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
                    (27 9 (:REWRITE UBDD-FIX-X-IS-X))
                    (18 18 (:TYPE-PRESCRIPTION UBDDP))
                    (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                    (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                    (9 9
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                    (7 7
                       (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                    (7 7 (:REWRITE BDD-IMPL-T))
                    (6 6
                       (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                    (2 2
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)))
(EVAL-BDD-TAKE-IND (58 28 (:REWRITE DEFAULT-+-2))
                   (39 28 (:REWRITE DEFAULT-+-1))
                   (30 3 (:DEFINITION LENGTH))
                   (24 6 (:REWRITE COMMUTATIVITY-OF-+))
                   (24 6 (:DEFINITION INTEGER-ABS))
                   (21 3 (:DEFINITION LEN))
                   (16 16
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                   (9 9 (:REWRITE DEFAULT-CDR))
                   (9 7 (:REWRITE DEFAULT-<-2))
                   (8 8 (:REWRITE FOLD-CONSTS-IN-+))
                   (8 7 (:REWRITE DEFAULT-<-1))
                   (7 7 (:REWRITE DEFAULT-CAR))
                   (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                   (3 3 (:TYPE-PRESCRIPTION LEN))
                   (3 3 (:REWRITE DEFAULT-REALPART))
                   (3 3 (:REWRITE DEFAULT-NUMERATOR))
                   (3 3 (:REWRITE DEFAULT-IMAGPART))
                   (3 3 (:REWRITE DEFAULT-DENOMINATOR))
                   (3 3 (:REWRITE DEFAULT-COERCE-2))
                   (3 3 (:REWRITE DEFAULT-COERCE-1))
                   (2 1
                      (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                   (1 1 (:REWRITE ZP-OPEN)))
(EVAL-BDD-OF-TAKE (1346 122 (:REWRITE TAKE-OF-LEN-FREE))
                  (710 106 (:DEFINITION LEN))
                  (371 213 (:REWRITE DEFAULT-+-2))
                  (274 274
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                  (213 213 (:REWRITE DEFAULT-+-1))
                  (180 40
                       (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
                  (130 43 (:REWRITE ZP-OPEN))
                  (117 62 (:REWRITE DEFAULT-<-2))
                  (90 90
                      (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                  (90 90
                      (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                  (90 90
                      (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                  (90 90
                      (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                  (88 29 (:REWRITE FOLD-CONSTS-IN-+))
                  (68 62 (:REWRITE DEFAULT-<-1))
                  (50 50 (:TYPE-PRESCRIPTION BDD-IMPL))
                  (40 10 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
                  (40 10
                      (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
                  (30 10 (:REWRITE UBDD-FIX-X-IS-X))
                  (20 20 (:TYPE-PRESCRIPTION UBDDP))
                  (20 20 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                  (20 20 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                  (10 10 (:REWRITE BDD-IMPL-T))
                  (2 2
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(BDD-EQUIV-IMPLIES-BDD-EQUIV-QCAR-1
     (104 104 (:REWRITE DEFAULT-CAR))
     (104 104
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (70 14
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (40 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (38 38
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (4 4 (:REWRITE DEFAULT-CDR)))
(BDD-EQUIV-IMPLIES-BDD-EQUIV-QCDR-1
     (104 104 (:REWRITE DEFAULT-CDR))
     (104 104
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (70 14
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (40 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (38 38
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (4 4 (:REWRITE DEFAULT-CAR)))
(TWO-BDD-IND (2930 1405 (:REWRITE DEFAULT-+-2))
             (2026 1405 (:REWRITE DEFAULT-+-1))
             (1460 146 (:DEFINITION LENGTH))
             (1168 292 (:DEFINITION INTEGER-ABS))
             (1022 146 (:DEFINITION LEN))
             (648 648
                  (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
             (438 334 (:REWRITE DEFAULT-<-2))
             (418 334 (:REWRITE DEFAULT-<-1))
             (340 340 (:REWRITE DEFAULT-CDR))
             (292 292 (:REWRITE DEFAULT-UNARY-MINUS))
             (194 194 (:REWRITE DEFAULT-CAR))
             (146 146 (:TYPE-PRESCRIPTION LEN))
             (146 146 (:REWRITE DEFAULT-REALPART))
             (146 146 (:REWRITE DEFAULT-NUMERATOR))
             (146 146 (:REWRITE DEFAULT-IMAGPART))
             (146 146 (:REWRITE DEFAULT-DENOMINATOR))
             (146 146 (:REWRITE DEFAULT-COERCE-2))
             (146 146 (:REWRITE DEFAULT-COERCE-1))
             (108 108 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
             (44 22
                 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP)))
(BDD-EQUIV-IMPLIES-EQUAL-BDD-MAX-DEPTH-1
     (84 84
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (72 22 (:REWRITE DEFAULT-+-2))
     (48 18 (:REWRITE UBDD-FIX-X-IS-X))
     (44 22 (:REWRITE DEFAULT-<-2))
     (44 22 (:REWRITE DEFAULT-<-1))
     (30 30 (:TYPE-PRESCRIPTION UBDDP))
     (23 23 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (23 23 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (22 22 (:REWRITE DEFAULT-+-1)))
(LEN-APPEND)
(CONS-MAKE-LIST (6 6
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                (4 1 (:REWRITE NATP-POSP))
                (2 2 (:TYPE-PRESCRIPTION NATP))
                (1 1 (:REWRITE POSP-RW))
                (1 1 (:REWRITE NATP-RW)))
(LEN-CONS-MAKE-LIST (36 36
                        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                    (16 5 (:REWRITE NATP-POSP))
                    (11 11 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
                    (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
                    (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
                    (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
                    (9 5 (:REWRITE POSP-RW))
                    (5 5 (:REWRITE EQUAL-CONSTANT-+))
                    (2 2 (:TYPE-PRESCRIPTION NATP))
                    (1 1 (:REWRITE NATP-RW))
                    (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(NTH-APPEND (230 230
                 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
            (128 64
                 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
            (64 64 (:TYPE-PRESCRIPTION TRUE-LISTP))
            (64 64 (:TYPE-PRESCRIPTION BINARY-APPEND))
            (60 20
                (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
            (44 44 (:META CANCEL_PLUS-LESSP-CORRECT))
            (23 23 (:META CANCEL_TIMES-EQUAL-CORRECT))
            (23 23 (:META CANCEL_PLUS-EQUAL-CORRECT))
            (13 7 (:REWRITE DEFAULT-UNARY-MINUS))
            (6 3 (:REWRITE <-0-+-NEGATIVE-2))
            (5 5 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
            (3 3
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(EVAL-BDD-DEPTH-APPEND (222 222
                            (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                       (126 28
                            (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
                       (62 62
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                       (62 62
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                       (62 62
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                       (62 62
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                       (35 35 (:TYPE-PRESCRIPTION BDD-IMPL))
                       (29 29 (:META CANCEL_PLUS-LESSP-CORRECT))
                       (28 7 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
                       (28 7
                           (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
                       (21 7 (:REWRITE UBDD-FIX-X-IS-X))
                       (16 8
                           (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                       (14 14 (:TYPE-PRESCRIPTION UBDDP))
                       (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                       (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-1))
                       (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
                       (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND))
                       (7 7 (:REWRITE BDD-IMPL-T))
                       (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
                       (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(CONS-MAKE-LIST-ELT-TO-TAIL (22 7 (:REWRITE NATP-POSP))
                            (13 7 (:REWRITE POSP-RW))
                            (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
                            (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
                            (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
                            (2 2 (:TYPE-PRESCRIPTION NATP))
                            (1 1
                               (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                            (1 1 (:REWRITE NATP-RW)))
(MAKE-LIST-CONS-MAKE-LIST (56 56
                              (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                          (20 2 (:REWRITE NATP-POSP))
                          (14 2 (:REWRITE POSP-RW))
                          (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
                          (6 2 (:REWRITE EQUAL-CONSTANT-+))
                          (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
                          (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
                          (4 2 (:REWRITE <-0-+-NEGATIVE-1))
                          (2 2 (:REWRITE ZP-OPEN))
                          (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(EVAL-BDD-DEPTH-IND (2 2
                       (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(EVAL-BDD-MAKE-LIST (82 13 (:REWRITE NATP-POSP))
                    (54 54
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                    (54 54
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                    (54 54
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                    (54 54
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                    (52 52
                        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                    (52 52
                        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                    (43 13 (:REWRITE POSP-RW))
                    (16 16 (:TYPE-PRESCRIPTION NATP))
                    (14 2 (:REWRITE NATP-POSP--1))
                    (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
                    (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
                    (12 6
                        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                    (12 4 (:REWRITE EQUAL-CONSTANT-+))
                    (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
                    (8 4 (:REWRITE <-0-+-NEGATIVE-1))
                    (7 7 (:REWRITE NATP-RW))
                    (6 6 (:REWRITE FOLD-CONSTS-IN-+))
                    (3 3
                       (:TYPE-PRESCRIPTION EVAL-BDD-DEPTH-IND)))
(EVAL-BDD-AP-MAKE-LIST (74 74
                           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                       (42 7 (:DEFINITION CONS-MAKE-LIST))
                       (28 28
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                       (28 28
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                       (28 28
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                       (28 28
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                       (28 7 (:REWRITE NATP-POSP))
                       (26 2 (:REWRITE EVAL-BDD-DEPTH-APPEND))
                       (24 2 (:REWRITE EVAL-BDD-DEPTH))
                       (14 14 (:TYPE-PRESCRIPTION NATP))
                       (14 14 (:TYPE-PRESCRIPTION LEN))
                       (12 4 (:DEFINITION LEN))
                       (12 2 (:REWRITE CONSP-OF-APPEND))
                       (8 8 (:TYPE-PRESCRIPTION MAX-DEPTH))
                       (8 8 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
                       (7 7 (:REWRITE POSP-RW))
                       (7 7 (:REWRITE NATP-RW))
                       (6 2 (:REWRITE CAR-OF-APPEND))
                       (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
                       (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
                       (4 4 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
                       (4 4 (:META CANCEL_PLUS-LESSP-CORRECT)))
(QV-PLUS-ONE (14 4 (:REWRITE NATP-POSP))
             (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
             (6 4 (:REWRITE POSP-RW))
             (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
             (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
             (4 4 (:TYPE-PRESCRIPTION NATP))
             (2 2 (:REWRITE NATP-RW)))
(NTH-LEN-LST (51 51
                 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
             (34 34
                 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
             (15 15 (:META CANCEL_PLUS-LESSP-CORRECT))
             (5 5 (:REWRITE ZP-OPEN))
             (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
             (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(COUNT-DOWN-TWO (8 8
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(NTH-CONS-MAKE-LIST (321 27 (:REWRITE LEN-CONS-MAKE-LIST))
                    (226 226
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                    (160 16 (:REWRITE NATP-POSP))
                    (112 16 (:REWRITE POSP-RW))
                    (53 53 (:META CANCEL_TIMES-EQUAL-CORRECT))
                    (53 53 (:META CANCEL_PLUS-EQUAL-CORRECT))
                    (48 16 (:REWRITE EQUAL-CONSTANT-+))
                    (19 19 (:REWRITE DEFAULT-UNARY-MINUS))
                    (12 6 (:REWRITE ASSOCIATIVITY-OF-+))
                    (3 3 (:TYPE-PRESCRIPTION COUNT-DOWN-TWO)))
(SUFFIXP-TRANSITIVE-3 (18 3 (:DEFINITION SUFFIXP))
                      (6 6
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
                      (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(SUFFIXP-TRANSITIVE-4)
(SUFFIXP-LEN-<= (30 30
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                (11 11 (:REWRITE SUFFIXP-TRANSITIVE))
                (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
                (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(SUFFIXP-LEN (22 22
                 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
             (7 7 (:REWRITE SUFFIXP-TRANSITIVE))
             (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
             (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
             (4 4 (:META CANCEL_PLUS-LESSP-CORRECT)))
(AIG-Q-COMPOSE-AIG-AND
     (405 9 (:DEFINITION AIG-Q-COMPOSE))
     (288 36 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (201 49 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (144 63 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (136 136
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (116 4 (:DEFINITION AIG-EVAL))
     (108 36 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (100 100
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (72 72 (:TYPE-PRESCRIPTION BOOLEANP))
     (72 4 (:DEFINITION AIG-ENV-LOOKUP))
     (42 6
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (36 9 (:DEFINITION Q-NOT))
     (36 3 (:DEFINITION BDD-EVAL-ALST))
     (30 30
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (28 4
         (:REWRITE HONS-ASSOC-EQUAL-COMMUTES-BDD-EVAL-ALIST-TO-EVAL-BDD))
     (27 9 (:DEFINITION AIG-ALIST-LOOKUP))
     (24 6
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (21 21
         (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (19 11
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (15 15
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (15 15
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (15 15
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (15 15
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (13 13 (:DEFINITION HONS-GET))
     (10 2
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (9 9 (:DEFINITION HONS))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (2 2 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (2 2 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(BDD-MAX-DEPTH-Q-AND-UBDDP
     (3746 3746
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (1500 750
           (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1368 304
           (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (1281 1281 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1281 1281 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (380 380 (:TYPE-PRESCRIPTION BDD-IMPL))
     (304 76 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
     (304 76
          (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
     (152 152 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (152 152 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (143 143 (:REWRITE UBDDP-OF-Q-AND))
     (76 76 (:REWRITE BDD-IMPL-T)))
(BDD-MAX-DEPTH-Q-AND)
(BDD-MAX-DEPTH-Q-AND-BOUND (3 3 (:META CANCEL_PLUS-LESSP-CORRECT)))
(BDD-MAX-DEPTH-Q-NOT-UBDDP
     (1260 60 (:REWRITE NOT-CONSP-UBDD-FIX))
     (1080 240
           (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (920 920
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (530 220
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (312 312 (:META CANCEL_PLUS-LESSP-CORRECT))
     (300 300 (:TYPE-PRESCRIPTION BDD-IMPL))
     (240 60 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
     (240 60
          (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
     (196 196 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (120 120 (:TYPE-PRESCRIPTION BDD-EQUIV))
     (120 120 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (120 120 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (60 60 (:TYPE-PRESCRIPTION UBDD-FIX))
     (60 60 (:TYPE-PRESCRIPTION BOOLEANP))
     (60 60 (:REWRITE BDD-IMPL-T)))
(BDD-MAX-DEPTH-Q-NOT)
(BDD-MAX-DEPTH-AIG-Q-COMPOSE
     (88 2 (:DEFINITION AIG-Q-COMPOSE))
     (60 22 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (19 19 (:META CANCEL_PLUS-LESSP-CORRECT))
     (16 16 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 3 (:DEFINITION Q-NOT))
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (3 3 (:DEFINITION HONS)))
(ASSIGN-FOR-BDD-AL-REC)
(LENGTHEN-TO-N)
(ASSIGN-FOR-BDD-AL)
(LEN-ASSIGN-FOR-BDD-AL-REC
     (64 64
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (36 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (36 4 (:DEFINITION BINARY-APPEND))
     (34 34 (:LINEAR SUFFIXP-LEN))
     (30 30
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (8 8
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (4 4
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:REWRITE EQUAL-CONSTANT-+))
     (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(LEN-ASSIGN-FOR-BDD-AL (48 1 (:REWRITE NATP-POSP))
                       (36 36
                           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                       (18 1 (:REWRITE POSP-RW))
                       (18 1 (:REWRITE NATP-RW))
                       (16 16 (:LINEAR SUFFIXP-LEN))
                       (12 2
                           (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                       (12 1 (:REWRITE INVERSE-OF-+-AS=0))
                       (12 1 (:DEFINITION BINARY-APPEND))
                       (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
                       (7 1 (:REWRITE <-0-+-NEGATIVE-2))
                       (6 6 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
                       (6 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                       (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                       (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
                       (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
                       (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                       (1 1 (:TYPE-PRESCRIPTION NATP))
                       (1 1
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (27 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (24 3 (:DEFINITION BINARY-APPEND))
     (18 6 (:DEFINITION LEN))
     (15 15
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (13 13
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (13 13
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (13 13
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (13 13
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (13 13
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (8 8 (:LINEAR SUFFIXP-LEN))
     (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
     (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(ASSIGN-FOR-BDD-AL-DEPTH
     (154 3 (:DEFINITION ASSIGN-FOR-BDD-AL-REC))
     (69 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (62 62
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (58 6 (:DEFINITION BINARY-APPEND))
     (55 15
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (48 1 (:REWRITE NATP-POSP))
     (25 15
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (19 19 (:META CANCEL_PLUS-LESSP-CORRECT))
     (18 1 (:REWRITE POSP-RW))
     (18 1 (:REWRITE NATP-RW))
     (15 15 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (12 12 (:LINEAR SUFFIXP-LEN))
     (12 1 (:REWRITE INVERSE-OF-+-AS=0))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 9
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (7 1 (:REWRITE <-0-+-NEGATIVE-2))
     (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (5 5 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(ASSIGN-FOR-BDD-AL-DEPTH-HONS-ASSOC-EQUAL
     (12 6
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 2 (:DEFINITION LEN))
     (4 4
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (2 2 (:LINEAR SUFFIXP-LEN)))
(ASSIGN-FOR-BDD-AL-REC-EXTEND
     (74 7
         (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (56 56
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (45 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (41 5 (:DEFINITION BINARY-APPEND))
     (30 10 (:DEFINITION LEN))
     (25 25
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (7 7
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:LINEAR SUFFIXP-LEN))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV)))
(ASSIGN-FOR-BDD-AL-EXTEND
     (157 7
          (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (127 18 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (125 25
          (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (105 9 (:DEFINITION BINARY-APPEND))
     (86 86
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (75 25
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (42 14 (:DEFINITION LEN))
     (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (25 25 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
     (25 25 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (22 22 (:META CANCEL_PLUS-LESSP-CORRECT))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (7 7 (:REWRITE FOLD-CONSTS-IN-+))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (7 7
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:LINEAR SUFFIXP-LEN))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV)))
(ASSIGN-FOR-BDD-AL-REC-SHRINK
     (502 45
          (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (424 424
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (279 62 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (253 31 (:DEFINITION BINARY-APPEND))
     (165 3 (:REWRITE CAR-NTHCDR))
     (155 155
          (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (132 6 (:DEFINITION NTH))
     (129 6 (:REWRITE NTH-LEN-LST))
     (103 103 (:META CANCEL_PLUS-LESSP-CORRECT))
     (82 4 (:REWRITE EVAL-BDD-DEPTH))
     (64 14 (:REWRITE ZP-OPEN))
     (49 49
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (49 49
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (49 49
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (49 49
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (49 49
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (48 17
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (46 46 (:LINEAR SUFFIXP-LEN))
     (36 6 (:DEFINITION NFIX))
     (31 31 (:REWRITE FOLD-CONSTS-IN-+))
     (30 3 (:REWRITE NTH-IMPLIES-CONSP-NTHCDR))
     (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (16 16 (:TYPE-PRESCRIPTION MAX-DEPTH))
     (12 6 (:REWRITE <-0-+-NEGATIVE-2))
     (10 10
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (8 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 4 (:REWRITE <-0-+-NEGATIVE-1))
     (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION NFIX))
     (6 3 (:REWRITE <-+-NEGATIVE-0-2))
     (6 3 (:REWRITE <-+-NEGATIVE-0-1))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ASSIGN-FOR-BDD-AL-SHRINK
     (130 26 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (80 80
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (71 71 (:META CANCEL_PLUS-LESSP-CORRECT))
     (42 12 (:REWRITE ZP-OPEN))
     (31 31 (:REWRITE FOLD-CONSTS-IN-+))
     (26 26
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (26 26
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (26 26
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (26 26
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (26 26
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (26 13 (:DEFINITION NFIX))
     (24 24 (:LINEAR SUFFIXP-LEN))
     (13 13 (:TYPE-PRESCRIPTION NFIX))
     (12 6 (:REWRITE <-0-+-NEGATIVE-1))
     (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (10 9 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE CDR-CONS)))
(ASSIGN-FOR-BDD-AL-SUFFIX
     (84 3 (:REWRITE SUFFIXP-LEN))
     (60 60
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (16 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (8 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+)))
(BDDS-COMPATIBLE-FOR-AL)
(BDDS-COMPATIBLE-FOR-AL-NECC)
(BDD-EQUIV-IMPLIES-EQUAL-BDDS-COMPATIBLE-FOR-AL-1
     (60 4 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (50 10
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (42 14 (:DEFINITION LEN))
     (36 4 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (32 32 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (30 30 (:META CANCEL_PLUS-LESSP-CORRECT))
     (29 29
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (28 28
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (10 10 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (10 10 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (8 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (8 8 (:LINEAR SUFFIXP-LEN))
     (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(BDD-EQUIV-IMPLIES-EQUAL-BDDS-COMPATIBLE-FOR-AL-2
     (60 4 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (50 10
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (42 14 (:DEFINITION LEN))
     (36 4 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (32 32 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (30 30 (:META CANCEL_PLUS-LESSP-CORRECT))
     (29 29
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (28 28
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (10 10 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (10 10 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (8 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (8 8 (:LINEAR SUFFIXP-LEN))
     (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(BDDS-COMPATIBLE-FOR-AL-SELF
     (37 3 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (21 7 (:DEFINITION LEN))
     (14 14
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
     (8 8 (:LINEAR SUFFIXP-LEN))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC)))
(BDDS-COMPATIBLE-WITH-BOOLEAN
     (200 5 (:DEFINITION TAKE))
     (155 10 (:REWRITE TAKE-OF-LEN-FREE))
     (140 10 (:REWRITE TAKE-OF-TOO-MANY))
     (60 60
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (60 20 (:DEFINITION LEN))
     (40 40 (:LINEAR SUFFIXP-LEN))
     (30 10 (:REWRITE TAKE-WHEN-ATOM))
     (25 25 (:META CANCEL_PLUS-LESSP-CORRECT))
     (20 20
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (13 13
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (13 13 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (13 13 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (11 11
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (7 7
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (5 5 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE EQUAL-CONSTANT-+)))
(BDDS-COMPATIBLE-RW)
(BDDS-COMPATIBLE-Q-NOTS-COMPATIBLE
     (274 18 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (162 18 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (149 18 (:REWRITE BDDS-COMPATIBLE-RW))
     (144 144 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (128 128
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (104 26 (:DEFINITION Q-NOT))
     (83 83 (:META CANCEL_PLUS-LESSP-CORRECT))
     (38 38 (:LINEAR SUFFIXP-LEN))
     (37 37
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (37 37
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (37 37
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (37 37
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (35 35
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (28 28
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (26 26 (:DEFINITION HONS))
     (18 18
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (8 8 (:REWRITE BDD-MAX-DEPTH-Q-NOT))
     (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(BDDS-COMPATIBLE-Q-ANDS-COMPATIBLE
     (310 20 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (184 20 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (168 168 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (150 50 (:DEFINITION LEN))
     (110 110 (:META CANCEL_PLUS-LESSP-CORRECT))
     (106 106
          (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (100 100
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (86 86
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (80 20 (:REWRITE BDDS-COMPATIBLE-RW))
     (76 76 (:LINEAR SUFFIXP-LEN))
     (42 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (40 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (40 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (40 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (38 38
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (18 2 (:REWRITE BDD-MAX-DEPTH-Q-AND-BOUND))
     (17 17 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (17 17 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION QS-SUBSET))
     (2 2 (:LINEAR BDD-MAX-DEPTH-Q-AND-BOUND)))
(BDDS-COMPATIBLE-DEGENERATE-AND
     (566 14 (:DEFINITION TAKE))
     (398 28 (:REWRITE TAKE-OF-LEN-FREE))
     (350 28 (:REWRITE TAKE-OF-TOO-MANY))
     (180 60 (:DEFINITION LEN))
     (180 12 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (168 168
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (138 12 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (128 128 (:LINEAR SUFFIXP-LEN))
     (76 28 (:REWRITE TAKE-WHEN-ATOM))
     (62 62 (:META CANCEL_PLUS-LESSP-CORRECT))
     (56 56
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (32 32 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (32 32 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (26 26
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (24 24
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (24 24
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (14 14 (:REWRITE ZP-OPEN))
     (14 14 (:REWRITE EQUAL-CONSTANT-+))
     (14 14
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (10 10 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (10 10 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (10 10 (:REWRITE BDD-IMPL-NECC)))
(BDDS-COMPATIBLE-DEGENERATE-AND1
     (566 14 (:DEFINITION TAKE))
     (398 28 (:REWRITE TAKE-OF-LEN-FREE))
     (350 28 (:REWRITE TAKE-OF-TOO-MANY))
     (232 16 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (186 62 (:DEFINITION LEN))
     (184 16 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (172 172
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (132 132 (:LINEAR SUFFIXP-LEN))
     (76 28 (:REWRITE TAKE-WHEN-ATOM))
     (66 66 (:META CANCEL_PLUS-LESSP-CORRECT))
     (56 56
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (48 4 (:REWRITE BDD-MAX-DEPTH-Q-AND-BOUND))
     (38 38
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (35 35 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (35 35 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (32 32
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (30 6
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (25 25
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (14 14 (:REWRITE ZP-OPEN))
     (14 14 (:REWRITE EQUAL-CONSTANT-+))
     (12 12 (:TYPE-PRESCRIPTION UBDDP))
     (10 10
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (6 2
        (:REWRITE |(qs-subset y (q-and x y))|))
     (6 2
        (:REWRITE |(qs-subset x (q-and x y))|))
     (6 2
        (:REWRITE |(qs-subset (q-and x y) x)|))
     (4 4 (:LINEAR BDD-MAX-DEPTH-Q-AND-BOUND)))
(BDDS-COMPATIBLE-DEGENERATE-AND2
     (566 14 (:DEFINITION TAKE))
     (398 28 (:REWRITE TAKE-OF-LEN-FREE))
     (350 28 (:REWRITE TAKE-OF-TOO-MANY))
     (232 16 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (186 62 (:DEFINITION LEN))
     (184 16 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (172 172
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (132 132 (:LINEAR SUFFIXP-LEN))
     (76 28 (:REWRITE TAKE-WHEN-ATOM))
     (66 66 (:META CANCEL_PLUS-LESSP-CORRECT))
     (56 56
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (48 4 (:REWRITE BDD-MAX-DEPTH-Q-AND-BOUND))
     (40 40
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (38 38
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (35 35 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (35 35 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (31 31
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (30 6
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (14 14 (:REWRITE ZP-OPEN))
     (14 14 (:REWRITE EQUAL-CONSTANT-+))
     (10 10
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (8 8 (:TYPE-PRESCRIPTION UBDDP))
     (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (6 6 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (6 2
        (:REWRITE |(qs-subset x (q-and x y))|))
     (6 2
        (:REWRITE |(qs-subset (q-and x y) y)|))
     (4 4 (:LINEAR BDD-MAX-DEPTH-Q-AND-BOUND)))
(BDDS-COMPATIBLE-FOR-AL-EXTEND
     (14 5 (:DEFINITION LEN))
     (12 1 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (8 8
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
     (4 4 (:LINEAR SUFFIXP-LEN))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (2 2
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (2 1 (:REWRITE COMMUTATIVITY-2-OF-+))
     (1 1 (:REWRITE NATP-RW))
     (1 1 (:REWRITE CDR-CONS)))
(BDDS-COMPATIBLE-FOR-AL-SUFFIX
     (99 33 (:DEFINITION LEN))
     (81 9 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (72 72
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (40 40 (:META CANCEL_PLUS-LESSP-CORRECT))
     (18 18
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (18 18
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (18 18
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (18 18
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (18 18
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (18 3 (:DEFINITION SUFFIXP))
     (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (8 8
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (8 8
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (6 6 (:REWRITE SUFFIXP-TRANSITIVE))
     (3 3 (:REWRITE NATP-RW)))
(BDDS-COMPATIBLE-FOR-AL-CONS
     (6 2 (:DEFINITION LEN))
     (4 4
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (2 2 (:REWRITE SUFFIXP-TRANSITIVE))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-NECC))
     (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
     (2 2 (:LINEAR SUFFIXP-LEN))
     (1 1 (:REWRITE NATP-RW)))
(ABS-BDD-AL-OKP)
(BDD-MAX-DEPTH-QV (222 222
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                  (108 36
                       (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                  (76 76 (:META CANCEL_PLUS-LESSP-CORRECT))
                  (74 74 (:TYPE-PRESCRIPTION UBDD-FIX))
                  (54 15 (:REWRITE NATP-POSP))
                  (23 23 (:META CANCEL_TIMES-EQUAL-CORRECT))
                  (21 15 (:REWRITE POSP-RW))
                  (18 18 (:TYPE-PRESCRIPTION NATP))
                  (9 9 (:REWRITE NATP-RW))
                  (1 1
                     (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(ABS-BDD-AL-OKP-CONS (18 18
                         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (18 6 (:DEFINITION LEN))
                     (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
                     (2 2 (:LINEAR SUFFIXP-LEN))
                     (2 1
                        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                     (1 1 (:TYPE-PRESCRIPTION ATOM-LISTP))
                     (1 1 (:REWRITE NATP-RW))
                     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
                     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-UBDDP
     (152 152
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (84 28 (:DEFINITION LEN))
     (55 5
         (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-UBDDP))
     (50 5
         (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-UBDDP))
     (40 5 (:DEFINITION APQS-MEMO-WFP))
     (35 5 (:DEFINITION ABS-FMEMO-WFP))
     (28 14
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (25 25 (:TYPE-PRESCRIPTION APQS-MEMO-WFP))
     (25 25 (:TYPE-PRESCRIPTION ABS-FMEMO-WFP))
     (15 15 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (15 15 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 6 (:LINEAR SUFFIXP-LEN)))
(ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-CONSP
     (98 98
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (42 14 (:DEFINITION LEN))
     (36 17
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (14 14 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (14 14 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (7 7 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 6 (:REWRITE NATP-RW)))
(ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH
     (2069 52 (:DEFINITION BDD-MAX-DEPTH))
     (883 42 (:REWRITE NOT-CONSP-UBDD-FIX))
     (757 168
          (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (576 576
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (416 52 (:DEFINITION MAX))
     (234 52 (:REWRITE UBDD-FIX-X-IS-X))
     (230 112
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (210 210 (:TYPE-PRESCRIPTION BDD-IMPL))
     (175 52 (:DEFINITION QCDR$INLINE))
     (175 52 (:DEFINITION QCAR$INLINE))
     (168 42 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
     (168 42
          (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
     (97 97 (:TYPE-PRESCRIPTION UBDDP))
     (87 47
         (:TYPE-PRESCRIPTION ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-CONSP))
     (84 84 (:TYPE-PRESCRIPTION BDD-EQUIV))
     (84 84 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (84 84 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (50 50 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (50 50 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (42 42 (:TYPE-PRESCRIPTION UBDD-FIX))
     (42 42 (:REWRITE BDD-IMPL-T))
     (40 40 (:TYPE-PRESCRIPTION NATP))
     (26 26 (:LINEAR SUFFIXP-LEN))
     (18 18 (:REWRITE FOLD-CONSTS-IN-+))
     (13 11
         (:REWRITE ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-UBDDP))
     (11 11
         (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (11 1
         (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-UBDDP))
     (10 1
         (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-UBDDP))
     (8 1 (:DEFINITION APQS-MEMO-WFP))
     (7 1 (:DEFINITION ABS-FMEMO-WFP))
     (5 5 (:TYPE-PRESCRIPTION APQS-MEMO-WFP))
     (5 5 (:TYPE-PRESCRIPTION ABS-FMEMO-WFP))
     (1 1
        (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL-TRANS-1)))
(ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH-RW
     (10 1 (:DEFINITION HONS-ASSOC-EQUAL))
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (3 1 (:DEFINITION LEN))
     (3 1 (:DEFINITION HONS-EQUAL))
     (2 1
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1 1
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH-X
     (52 52
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (14 14 (:LINEAR SUFFIXP-LEN))
     (14 7
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (11 11 (:META CANCEL_PLUS-LESSP-CORRECT))
     (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+)))
(EVAL-BDD-ASSIGN-FOR-BDD-AL
     (1488 34 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (1310 1310
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (1300 34 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (1071 102
           (:REWRITE ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH-X))
     (1028 374 (:DEFINITION LEN))
     (970 27
          (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (450 90
          (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (450 66 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (381 33 (:DEFINITION BINARY-APPEND))
     (270 90
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (244 122
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (186 4
          (:REWRITE ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH-RW))
     (173 173 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (173 173 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (109 109 (:REWRITE FOLD-CONSTS-IN-+))
     (102 102
          (:TYPE-PRESCRIPTION ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-CONSP))
     (100 100 (:LINEAR SUFFIXP-LEN))
     (90 90 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (90 90 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
     (90 90 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (86 62
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (63 63
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (63 63
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (63 63
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (63 63
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (39 2 (:REWRITE NTH-LEN-LST))
     (36 1 (:REWRITE ABS-BDD-AL-OKP-CONS))
     (34 34 (:REWRITE BDDS-COMPATIBLE-RW))
     (33 17 (:REWRITE DEFAULT-UNARY-MINUS))
     (31 31 (:TYPE-PRESCRIPTION NFIX))
     (31 1 (:REWRITE EVAL-BDD-DEPTH))
     (21 21
         (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (6 6
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (4 4 (:TYPE-PRESCRIPTION MAX-DEPTH)))
(ABS-BDD-AL-OKP-BDD-COMPATIBLE-HONS-ASSOC-EQUAL
     (26 1 (:DEFINITION ABS-BDD-AL-OKP))
     (14 14
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (12 4 (:DEFINITION LEN))
     (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
     (3 3 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (2 2 (:TYPE-PRESCRIPTION QV))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (2 2
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (2 2
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (2 2 (:LINEAR SUFFIXP-LEN))
     (2 1
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1 1 (:REWRITE NATP-RW))
     (1 1
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(NTH-ASSIGN-FOR-BDD-AL-REC-ABOVE-VARS
     (398 398
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (248 164 (:META CANCEL_PLUS-LESSP-CORRECT))
     (241 21
          (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (117 26 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (109 13 (:DEFINITION BINARY-APPEND))
     (80 80 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (76 76
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (54 54 (:LINEAR SUFFIXP-LEN))
     (43 36 (:REWRITE DEFAULT-UNARY-MINUS))
     (30 8
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (24 2 (:REWRITE LEN-APPEND))
     (23 21
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (21 21
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (21 21
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (21 21
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (21 21
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (10 10
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (5 5 (:REWRITE NATP-RW))
     (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION QS-SUBSET))
     (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(NTH-ASSIGN-FOR-BDD-AL-REC-BELOW-VARS
     (118 118
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (112 38 (:DEFINITION LEN))
     (66 66 (:META CANCEL_PLUS-LESSP-CORRECT))
     (56 56
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (38 38 (:LINEAR SUFFIXP-LEN))
     (30 3
         (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (27 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (27 3 (:DEFINITION BINARY-APPEND))
     (23 23
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (12 12 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (12 1 (:REWRITE LEN-APPEND))
     (6 6
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (4 4
        (:REWRITE NTH-ASSIGN-FOR-BDD-AL-REC-ABOVE-VARS))
     (4 4 (:REWRITE NATP-RW))
     (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (4 3 (:REWRITE COMMUTATIVITY-OF-+))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (3 3
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (3 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(NTH-ASSIGN-FOR-BDD-AL-REC
     (416 6 (:DEFINITION ASSIGN-FOR-BDD-AL-REC))
     (414 20 (:REWRITE NTH-LEN-LST))
     (316 13 (:DEFINITION NTH))
     (188 188
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (180 60 (:DEFINITION LEN))
     (178 3 (:REWRITE CAR-NTHCDR))
     (143 83 (:META CANCEL_PLUS-LESSP-CORRECT))
     (125 117
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (95 9
         (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (91 18 (:DEFINITION NFIX))
     (65 3
         (:REWRITE ASSIGN-FOR-BDD-AL-REC-SHRINK))
     (59 19 (:REWRITE <-+-NEGATIVE-0-1))
     (54 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (51 6 (:DEFINITION BINARY-APPEND))
     (40 40 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (34 34 (:REWRITE FOLD-CONSTS-IN-+))
     (32 32
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (31 7 (:REWRITE ZP-OPEN))
     (30 30 (:LINEAR SUFFIXP-LEN))
     (18 14 (:REWRITE DEFAULT-UNARY-MINUS))
     (18 6
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (18 4
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (12 3 (:REWRITE NTH-IMPLIES-CONSP-NTHCDR))
     (12 3 (:DEFINITION NTHCDR))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 9
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (8 6 (:DEFINITION FIX))
     (8 1 (:REWRITE LEN-ASSIGN-FOR-BDD-AL-REC))
     (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (6 6
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (6 3 (:REWRITE <-0-+-NEGATIVE-1))
     (6 2
        (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (6 2 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
     (4 2
        (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
     (4 2
        (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
     (3 3 (:REWRITE NATP-RW))
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(NTH-ABS-BDD-AL-OKP-DEPTH
     (105 8 (:REWRITE NTH-LEN-LST))
     (86 86
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (40 40 (:META CANCEL_PLUS-LESSP-CORRECT))
     (30 30 (:LINEAR SUFFIXP-LEN))
     (23 7 (:DEFINITION NFIX))
     (14 7
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (13 13 (:REWRITE FOLD-CONSTS-IN-+))
     (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (6 6 (:REWRITE ZP-OPEN))
     (6 3 (:REWRITE <-+-NEGATIVE-0-1))
     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 4 (:REWRITE NATP-RW)))
(NTH-ASSIGN-FOR-BDD-AL-REC-ABS-BDD-AL-OKP
     (694 33 (:REWRITE NTH-LEN-LST))
     (541 19 (:DEFINITION NTH))
     (536 8 (:DEFINITION ASSIGN-FOR-BDD-AL-REC))
     (378 126 (:DEFINITION LEN))
     (366 366
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (162 31 (:DEFINITION NFIX))
     (140 39 (:REWRITE <-+-NEGATIVE-0-1))
     (123 3 (:REWRITE CAR-NTHCDR))
     (87 3 (:DEFINITION ABS-BDD-AL-OKP))
     (86 13 (:REWRITE ZP-OPEN))
     (72 16 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (66 66 (:REWRITE FOLD-CONSTS-IN-+))
     (65 8 (:DEFINITION BINARY-APPEND))
     (47 34 (:REWRITE DEFAULT-UNARY-MINUS))
     (46 46 (:LINEAR SUFFIXP-LEN))
     (40 40
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (22 11 (:REWRITE <-0-+-NEGATIVE-1))
     (16 6
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (14 14
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (14 14
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (14 14
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (14 14
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (13 13
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (10 3 (:REWRITE NTH-IMPLIES-CONSP-NTHCDR))
     (10 3 (:DEFINITION NTHCDR))
     (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (6 6 (:TYPE-PRESCRIPTION QV))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (2 2 (:REWRITE NATP-RW))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (1 1 (:REWRITE SUFFIXP-TRANSITIVE))
     (1 1 (:REWRITE EVAL-BDD-OF-NIL)))
(NTH-ASSIGN-FOR-BDD-AL-BDD-AL-OKP
     (206 3 (:DEFINITION ASSIGN-FOR-BDD-AL-REC))
     (175 9 (:REWRITE NTH-LEN-LST))
     (174 5
          (:REWRITE EVAL-ASSIGN-FOR-BDD-AL-REC-AT-LESS-DEPTH))
     (124 4 (:DEFINITION NTH))
     (120 120
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (102 34 (:DEFINITION LEN))
     (75 15
         (:TYPE-PRESCRIPTION ASSIGN-FOR-BDD-AL-REC))
     (75 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (68 68
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (61 5 (:DEFINITION BINARY-APPEND))
     (45 15
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (44 2 (:LINEAR NTH-ABS-BDD-AL-OKP-DEPTH))
     (28 10 (:REWRITE <-+-NEGATIVE-0-1))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+))
     (20 4 (:REWRITE ZP-OPEN))
     (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (15 15 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
     (15 15 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (12 12 (:LINEAR SUFFIXP-LEN))
     (12 9 (:REWRITE DEFAULT-UNARY-MINUS))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (5 5
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 2 (:REWRITE <-0-+-NEGATIVE-1))
     (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (2 2 (:REWRITE NATP-RW))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (2 1
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1 1 (:TYPE-PRESCRIPTION ATOM-LISTP)))
(BDDS-COMPATIBLE-FOR-AL-EXTEND-FOR-X
     (82 82
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (52 2 (:DEFINITION ABS-BDD-AL-OKP))
     (46 3 (:REWRITE NTH-LEN-LST))
     (42 4 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (33 1 (:DEFINITION NTH))
     (27 3 (:REWRITE ASSIGN-FOR-BDD-AL-DEPTH))
     (24 2
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-EXTEND))
     (24 2
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-CONS))
     (8 8 (:REWRITE FOLD-CONSTS-IN-+))
     (8 8 (:LINEAR SUFFIXP-LEN))
     (6 6
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (6 1 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE SUFFIXP-TRANSITIVE))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (5 5
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (4 4
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (4 2
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (3 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (2 2 (:REWRITE NATP-RW))
     (2 1 (:REWRITE <-+-NEGATIVE-0-1)))
(ABS-MEMO-OKP)
(ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR
     (1134 21 (:DEFINITION AIG-Q-COMPOSE))
     (672 84 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (441 105
          (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (294 294
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (294 147
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (292 292
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (273 21 (:DEFINITION AIG-ALIST-LOOKUP))
     (252 252
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (252 84 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (231 21 (:DEFINITION HONS-GET))
     (168 168 (:TYPE-PRESCRIPTION BOOLEANP))
     (147 21
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (84 21
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (84 21 (:DEFINITION Q-NOT))
     (68 34
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (62 62 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (62 62 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (52 52 (:TYPE-PRESCRIPTION QV))
     (35 7
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (26 26 (:META CANCEL_PLUS-LESSP-CORRECT))
     (21 21 (:DEFINITION HONS))
     (14 14 (:TYPE-PRESCRIPTION BDD-IMPL))
     (7 7
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (7 7
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (5 5
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (2 2 (:LINEAR SUFFIXP-LEN))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ABS-MEMO-OKP-HONS-ASSOC-EQUAL-RW1
     (1458 27 (:DEFINITION AIG-Q-COMPOSE))
     (864 108 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (567 135
          (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (378 378
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (378 189
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (351 27 (:DEFINITION AIG-ALIST-LOOKUP))
     (324 324
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (324 108 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (297 27 (:DEFINITION HONS-GET))
     (252 252
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (216 216 (:TYPE-PRESCRIPTION BOOLEANP))
     (189 27
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (108 27
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (108 27 (:DEFINITION Q-NOT))
     (80 40
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (61 61 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (61 61 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (35 7
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (27 27 (:DEFINITION HONS))
     (21 7 (:DEFINITION LEN))
     (16 13
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (14 14 (:TYPE-PRESCRIPTION BDD-IMPL))
     (13 13
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (7 7 (:META CANCEL_PLUS-LESSP-CORRECT))
     (5 5
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (2 2 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE NATP-RW)))
(ABS-MEMO-OKP-HONS-ASSOC-EQUAL-RW2
     (10 1 (:DEFINITION HONS-ASSOC-EQUAL))
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (3 1 (:DEFINITION LEN))
     (3 1 (:DEFINITION HONS-EQUAL))
     (2 1
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1 1
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(ABS-MEMO-OKP-HONS-ASSOC-EQUAL-RW3
     (1586 192 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (1245 5
           (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW2))
     (1230 5 (:DEFINITION ABS-FMEMO-OKP))
     (1034 240
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (683 336
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (672 672
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (582 192 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (576 576
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (388 388
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (384 384 (:TYPE-PRESCRIPTION BOOLEANP))
     (354 48
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (201 48
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (192 48 (:DEFINITION Q-NOT))
     (122 61
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (103 103 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (103 103 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (48 48 (:DEFINITION HONS))
     (25 25 (:TYPE-PRESCRIPTION ABS-FMEMO-OKP))
     (25 25 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (25 25 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (21 7 (:DEFINITION LEN))
     (7 7
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (7 7
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (7 7 (:META CANCEL_PLUS-LESSP-CORRECT)))
(ABS-MEMO-OKP-EXTEND-BDD-AL
     (1817 228 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (1191 283
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (793 793
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (791 396
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (682 228 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (678 678
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (454 454 (:TYPE-PRESCRIPTION BOOLEANP))
     (393 57
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (290 290
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (228 57 (:DEFINITION Q-NOT))
     (225 57
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (114 22
          (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (100 12
          (:REWRITE BDDS-COMPATIBLE-FOR-AL-EXTEND))
     (57 57 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (57 57 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (57 57 (:DEFINITION HONS))
     (37 37 (:META CANCEL_PLUS-LESSP-CORRECT))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (22 22 (:REWRITE FOLD-CONSTS-IN-+))
     (22 22
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (22 22 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (22 22 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (12 12 (:LINEAR SUFFIXP-LEN))
     (8 8 (:TYPE-PRESCRIPTION SUFFIXP))
     (8 8 (:REWRITE SUFFIXP-TRANSITIVE))
     (8 8 (:REWRITE SUFFIXP-OF-SELF))
     (6 6 (:REWRITE NATP-RW))
     (6 6
        (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR)))
(ABS-MEMO-OKP-CONSP-CDR-HONS-ASSOC-EQUAL
     (3780 70 (:DEFINITION AIG-Q-COMPOSE))
     (3340 10
           (:REWRITE APQS-MEMO-OKP-CONSP-CDR-HONS-ASSOC-EQUAL))
     (3310 10 (:DEFINITION APQS-MEMO-OKP))
     (2240 280 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (1470 350
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (980 980
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (980 490
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (910 70 (:DEFINITION AIG-ALIST-LOOKUP))
     (840 840
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (840 280 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (770 70 (:DEFINITION HONS-GET))
     (600 600
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (560 560 (:TYPE-PRESCRIPTION BOOLEANP))
     (490 70
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (280 70
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (280 70 (:DEFINITION Q-NOT))
     (182 91
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (162 162 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (162 162 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (140 20
          (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (100 100 (:TYPE-PRESCRIPTION BDD-IMPL))
     (80 50 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (70 70 (:DEFINITION HONS))
     (50 50 (:TYPE-PRESCRIPTION APQS-MEMO-OKP))
     (50 50 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (30 10 (:DEFINITION LEN))
     (10 10
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (10 10
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (10 10 (:META CANCEL_PLUS-LESSP-CORRECT)))
(BDDS-COMPATIBLE-BDD-MAX-DEPTH-IMPLIES-EQUIV
     (172 4 (:DEFINITION TAKE))
     (114 8 (:REWRITE TAKE-OF-LEN-FREE))
     (92 8 (:REWRITE TAKE-OF-TOO-MANY))
     (42 14 (:DEFINITION LEN))
     (40 40
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (32 32 (:LINEAR SUFFIXP-LEN))
     (32 2 (:REWRITE ASSIGN-FOR-BDD-AL-SUFFIX))
     (20 8 (:REWRITE TAKE-WHEN-ATOM))
     (18 18 (:META CANCEL_PLUS-LESSP-CORRECT))
     (16 16
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (16 16
         (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (12 12
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (5 5
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (5 5
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE EQUAL-CONSTANT-+)))
(ABS-MEMO-OKP-BDD-MAX-DEPTH-IMPLIES-EQUAL-Q-COMPOSE
     (484 11 (:DEFINITION AIG-Q-COMPOSE))
     (338 44 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (298 3
          (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (287 1
          (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL))
     (284 1 (:DEFINITION APQS-MEMO-OKP))
     (219 51 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (144 144
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (140 71 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (128 44 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (120 120
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (84 84 (:TYPE-PRESCRIPTION BOOLEANP))
     (65 11
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (44 11 (:DEFINITION Q-NOT))
     (40 40
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (38 11
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (33 11 (:DEFINITION AIG-ALIST-LOOKUP))
     (33 1
         (:LINEAR ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH))
     (30 1 (:DEFINITION ABS-BDD-AL-OKP))
     (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (11 11 (:DEFINITION HONS-GET))
     (11 11 (:DEFINITION HONS))
     (9 3 (:DEFINITION LEN))
     (5 5 (:TYPE-PRESCRIPTION APQS-MEMO-OKP))
     (5 5 (:TYPE-PRESCRIPTION ABS-BDD-AL-OKP))
     (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION QV))
     (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (4 4 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (4 4
        (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (3 1 (:DEFINITION HONS-EQUAL))
     (2 1
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1 1
        (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL-TRANS-1))
     (1 1
        (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR)))
(MAX-DEPTH-WHEN-BDD-EQUIV-AIG-Q-COMPOSE
     (44 1 (:DEFINITION AIG-Q-COMPOSE))
     (32 4 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (21 5 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (14 14
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (14 7 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (12 12
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (12 4 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (7 1
        (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (4 1
        (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (4 1 (:DEFINITION Q-NOT))
     (3 1 (:DEFINITION AIG-ALIST-LOOKUP))
     (2 2
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (1 1 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (1 1 (:DEFINITION HONS-GET))
     (1 1 (:DEFINITION HONS)))
(Q-AND-SELF (21 5
                (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
            (8 8
               (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
            (8 2 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
            (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-2))
            (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-1))
            (3 1 (:REWRITE Q-AND-OF-SELF-AGGRESSIVE))
            (2 2 (:TYPE-PRESCRIPTION UBDDP))
            (2 2
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
            (2 2
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
            (2 2
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
            (2 2
               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1)))
(LEN-CONS-OPEN (6 6 (:LINEAR SUFFIXP-LEN))
               (4 4
                  (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
               (3 3
                  (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR)))
(AND-BDDIFY-VAR-WEAKENING-OK
     (3164 452
           (:REWRITE BDDS-COMPATIBLE-FOR-AL-EXTEND))
     (2655 2655 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (2655 2655 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (1565 1565 (:REWRITE NATP-RW))
     (1554 1554
           (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
     (1196 1196 (:REWRITE FOLD-CONSTS-IN-+))
     (480 480
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (480 240 (:REWRITE DEFAULT-*-2))
     (480 240 (:REWRITE DEFAULT-*-1))
     (464 232 (:LINEAR X*Y>1-POSITIVE))
     (62 62
         (:REWRITE ABS-MEMO-OKP-HONS-ASSOC-EQUAL-RW2)))
(AND-BDDIFY-VAR-WEAKENING-SUFFIXP-RW)
(AIG-BDDIFY-VAR-WEAKENING-INDUCT
     (60 20 (:DEFINITION INTEGER-ABS))
     (60 10 (:DEFINITION LENGTH))
     (48 12 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (40 40
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (30 10 (:DEFINITION LEN))
     (30 6 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (26 26 (:REWRITE FOLD-CONSTS-IN-+))
     (24 3 (:DEFINITION MEMBER-EQUAL))
     (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
     (18 18
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (10 10 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (10 10 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (10 10 (:REWRITE DEFAULT-REALPART))
     (10 10 (:REWRITE DEFAULT-NUMERATOR))
     (10 10 (:REWRITE DEFAULT-IMAGPART))
     (10 10 (:REWRITE DEFAULT-DENOMINATOR))
     (10 10 (:REWRITE DEFAULT-COERCE-2))
     (10 10 (:REWRITE DEFAULT-COERCE-1))
     (8 8 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
     (6 6 (:REWRITE SUBSETP-MEMBER . 2))
     (6 6 (:REWRITE SUBSETP-MEMBER . 1))
     (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (3 3 (:REWRITE MEMBER-SELF))
     (1 1 (:REWRITE SUBSETP-TRANS2))
     (1 1 (:REWRITE SUBSETP-TRANS))
     (1 1 (:REWRITE NOT-AIG-ATOM-P-OF-CONS)))
(BDD-MAX-DEPTH-WHEN-BOOLEANP
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (1 1
        (:LINEAR MAX-DEPTH-WHEN-BDD-EQUIV-AIG-Q-COMPOSE)))
(FMEMO-OK-OF-AIG-BDDIFY-VAR-WEAKENING-CACHE-INSERT
     (260 36 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (228 36
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (224 96 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (192 192
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (192 64 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (160 160
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (132 36
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (100 36 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (64 64 (:TYPE-PRESCRIPTION BOOLEANP))
     (48 48
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (31 31 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (31 31 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (12 6
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (6 6 (:TYPE-PRESCRIPTION ATOM-LISTP)))
(MEMO-OK-OF-AIG-BDDIFY-VAR-WEAKENING-CACHE-INSERT
     (137 18 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (120 18
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (119 51 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (102 102
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (102 34 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (85 85
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (69 18
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (52 18 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (40 40 (:TYPE-PRESCRIPTION BOOLEANP))
     (24 24
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (15 6
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (12 6
         (:REWRITE BDD-MAX-DEPTH-WHEN-BOOLEANP))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (7 7 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (4 4 (:LINEAR SUFFIXP-LEN))
     (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (3 3 (:REWRITE NATP-RW))
     (2 2
        (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR)))
(AIG-BDDIFY-VAR-WEAKENING-OK
     (5051 2056
           (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (1532 1532
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (647 647 (:META CANCEL_PLUS-LESSP-CORRECT))
     (500 250
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (414 4
          (:REWRITE ABS-MEMO-OKP-BDD-MAX-DEPTH-IMPLIES-EQUAL-Q-COMPOSE))
     (391 391 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (391 391 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (320 320 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (320 320 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (208 52
          (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
     (86 86
         (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
     (60 2
         (:LINEAR ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH))
     (56 14 (:DEFINITION Q-NOT))
     (14 14 (:DEFINITION HONS))
     (4 4
        (:REWRITE AND-BDDIFY-VAR-WEAKENING-OK))
     (3 3
        (:TYPE-PRESCRIPTION ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-CONSP))
     (2 2 (:TYPE-PRESCRIPTION Q-NOT)))
(ABS-ARGS-OKP)
(AIG-BDDIFY-VAR-WEAKENING-OK-IF-ARGS-OK
     (707 16 (:DEFINITION AIG-Q-COMPOSE))
     (498 64 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (454 2 (:DEFINITION ABS-MEMO-OKP))
     (438 2 (:DEFINITION ABS-FMEMO-OKP))
     (325 77 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (216 216
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (213 106
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (188 64 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (180 180
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (124 124 (:TYPE-PRESCRIPTION BOOLEANP))
     (104 104
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (99 15
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (64 16 (:DEFINITION Q-NOT))
     (57 15
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (52 2 (:DEFINITION ABS-BDD-AL-OKP))
     (48 16 (:DEFINITION AIG-ALIST-LOOKUP))
     (42 14 (:DEFINITION LEN))
     (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (16 16
         (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (16 16 (:DEFINITION HONS-GET))
     (16 16 (:DEFINITION HONS))
     (12 6
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (11 11 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (11 11 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (2 2
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX)))
(AIG-BDDIFY-VAR-WEAKENING-OK-IF-ARGS-OK-2
     (355 8 (:DEFINITION AIG-Q-COMPOSE))
     (249 32 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (227 1 (:DEFINITION ABS-MEMO-OKP))
     (219 1 (:DEFINITION ABS-FMEMO-OKP))
     (163 39 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (109 109
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (108 53 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (94 32 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (90 90
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (62 62 (:TYPE-PRESCRIPTION BOOLEANP))
     (50 50
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (49 7
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (32 8 (:DEFINITION Q-NOT))
     (28 7
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (26 1 (:DEFINITION ABS-BDD-AL-OKP))
     (24 8 (:DEFINITION AIG-ALIST-LOOKUP))
     (18 6 (:DEFINITION LEN))
     (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (8 8 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (8 8 (:DEFINITION HONS-GET))
     (8 8 (:DEFINITION HONS))
     (6 6 (:TYPE-PRESCRIPTION LEN))
     (6 6 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (5 5 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (5 5 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
     (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (1 1
        (:TYPE-PRESCRIPTION BDDS-COMPATIBLE-FOR-AL))
     (1 1
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (1 1
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (1 1
        (:REWRITE AIG-BDDIFY-VAR-WEAKENING-OK-IF-ARGS-OK)))
(ABS-ARGS-OKP-START (2 2 (:META CANCEL_PLUS-LESSP-CORRECT)))
(UBDD-LISTP-AIG-Q-COMPOSE-LIST
     (141 3 (:DEFINITION AIG-Q-COMPOSE))
     (96 12 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (63 15 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (42 42
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (36 15 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (36 12 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (28 4 (:DEFINITION UBDDP-VAL-ALISTP))
     (24 24 (:TYPE-PRESCRIPTION BOOLEANP))
     (24 24
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (24 4 (:REWRITE UBDD-LISTP-WHEN-ATOM))
     (12 12
         (:TYPE-PRESCRIPTION AIG-Q-COMPOSE-LIST))
     (12 3 (:DEFINITION Q-NOT))
     (9 3 (:DEFINITION AIG-ALIST-LOOKUP))
     (8 4
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (3 3 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (3 3 (:DEFINITION HONS-GET))
     (3 3 (:DEFINITION HONS)))
(MAX-DEPTH-GTE-BDD-MAX-DEPTH
     (711 237 (:REWRITE UBDD-FIX-X-IS-X))
     (474 474 (:TYPE-PRESCRIPTION UBDDP))
     (220 220
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (204 204 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (204 204 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (168 8 (:REWRITE NOT-CONSP-UBDD-FIX))
     (144 32
          (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (88 44
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (40 40 (:TYPE-PRESCRIPTION BDD-IMPL))
     (32 8 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T))
     (32 8
         (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
     (18 18 (:META CANCEL_PLUS-LESSP-CORRECT))
     (16 16 (:TYPE-PRESCRIPTION BDD-EQUIV))
     (16 16 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (16 16 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (8 8 (:REWRITE BDD-IMPL-T))
     (4 4
        (:LINEAR MAX-DEPTH-WHEN-BDD-EQUIV-AIG-Q-COMPOSE)))
(ABS-RECHECK-EXACTNESS-OK
     (1135 147 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (981 147
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (434 434
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (425 147 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (278 278 (:TYPE-PRESCRIPTION BOOLEANP))
     (136 4
          (:LINEAR ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-DEPTH))
     (124 4 (:DEFINITION ABS-BDD-AL-OKP))
     (96 32 (:DEFINITION LEN))
     (95 1
         (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL))
     (92 1 (:DEFINITION APQS-MEMO-OKP))
     (90 45
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (82 82 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (82 82 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (64 64 (:META CANCEL_PLUS-LESSP-CORRECT))
     (37 4
         (:REWRITE ABS-MEMO-OKP-BDD-MAX-DEPTH-IMPLIES-EQUAL-Q-COMPOSE))
     (20 20 (:TYPE-PRESCRIPTION ABS-BDD-AL-OKP))
     (17 17
         (:REWRITE ABS-FMEMO-OKP-HONS-ASSOC-EQUAL-RW1))
     (16 16 (:TYPE-PRESCRIPTION QV))
     (16 16
         (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (16 16
         (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX))
     (8 8
        (:LINEAR MAX-DEPTH-WHEN-BDD-EQUIV-AIG-Q-COMPOSE))
     (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (5 5 (:TYPE-PRESCRIPTION APQS-MEMO-OKP))
     (3 1 (:DEFINITION HONS-EQUAL))
     (1 1
        (:REWRITE APQS-MEMO-OKP-HONS-ASSOC-EQUAL-BDD-IMPL-TRANS-1)))
(ABS-RECHECK-EXACTNESS-TOP-FMEMO-OK
     (1056 24 (:DEFINITION AIG-Q-COMPOSE))
     (876 4 (:DEFINITION ABS-FMEMO-OKP))
     (768 96 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (681 3 (:DEFINITION ABS-MEMO-OKP))
     (504 120
          (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (336 336
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (336 168
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (288 288
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (288 96 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (192 192 (:TYPE-PRESCRIPTION BOOLEANP))
     (168 24
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (116 116
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (96 24
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (96 24 (:DEFINITION Q-NOT))
     (72 24 (:DEFINITION AIG-ALIST-LOOKUP))
     (70 14
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (24 24 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (24 24 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (24 24 (:DEFINITION HONS))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (14 14 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (14 7
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (9 9 (:TYPE-PRESCRIPTION LEN))
     (9 9 (:TYPE-PRESCRIPTION BDD-MAX-DEPTH))
     (9 3 (:DEFINITION LEN))
     (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 2
        (:REWRITE ABS-MEMO-OKP-BDD-MAX-DEPTH-IMPLIES-EQUAL-Q-COMPOSE))
     (3 3
        (:TYPE-PRESCRIPTION BDDS-COMPATIBLE-FOR-AL))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX)))
(ABS-RECHECK-EXACTNESS-TOP-ABS-ARGS-OKP
     (1120 140 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (735 175
          (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (490 490
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (490 245
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (420 420
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (420 140 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (280 280 (:TYPE-PRESCRIPTION BOOLEANP))
     (245 35
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (216 216
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (140 35
          (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (140 35 (:DEFINITION Q-NOT))
     (51 17 (:DEFINITION LEN))
     (39 39 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (39 39 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (35 35 (:DEFINITION HONS))
     (30 15
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (20 20 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (20 20 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (15 15 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
     (5 5
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (5 5
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX)))
(ABS-ARGS-OKP-CHANGE-FMEMO
     (576 72 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (378 90 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (252 252
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (252 126
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (216 216
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (216 72 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (144 144 (:TYPE-PRESCRIPTION BOOLEANP))
     (126 18
          (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (124 124
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (72 18
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (72 18 (:DEFINITION Q-NOT))
     (45 9
         (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (33 11 (:DEFINITION LEN))
     (21 21 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (21 21 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (18 18 (:TYPE-PRESCRIPTION BDD-IMPL))
     (18 18 (:DEFINITION HONS))
     (18 9
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (9 9 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (9 9 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (9 9 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-WITH-BOOLEAN))
     (3 3
        (:REWRITE BDDS-COMPATIBLE-FOR-AL-SUFFIX)))
(AIG-BDDIFY-LIST-VAR-WEAKENING-OK
     (2279 49 (:DEFINITION AIG-Q-COMPOSE))
     (1568 196 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (1029 245
           (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (686 686
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (604 261
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (588 196 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (424 424
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (392 392 (:TYPE-PRESCRIPTION BOOLEANP))
     (230 230
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (196 49 (:DEFINITION Q-NOT))
     (147 49 (:DEFINITION AIG-ALIST-LOOKUP))
     (56 8
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (49 49
         (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (49 49 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (49 49 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (49 49 (:DEFINITION HONS-GET))
     (49 49 (:DEFINITION HONS))
     (32 8
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (26 26 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (26 26 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (10 10 (:META CANCEL_PLUS-LESSP-CORRECT)))
(APQS-MEMO-OKP-ATOM (2 2
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)))
(ABS-FMEMO-OKP-ATOM (2 2
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)))
(AIG-BDDIFY-LIST-ITER1-OK
     (1058 1058
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (459 153
          (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (153 153 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (153 153 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (117 117 (:REWRITE ABS-FMEMO-OKP-ATOM))
     (98 98 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (98 98 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (67 67 (:META CANCEL_PLUS-LESSP-CORRECT))
     (12 12
         (:REWRITE ABS-ARGS-OKP-CHANGE-FMEMO)))
(LOOKUP-BDDIFY-EXTRACT-BOOL-ALIST-WHEN-NOT-IN-VALAL
     (406 406
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (202 101
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (108 108 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (108 108 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (34 34
         (:TYPE-PRESCRIPTION BDDIFY-EXTRACT-BOOL-ALIST)))
(CAR-HONS-ASSOC-EQUAL (44 44
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (24 12
                          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                      (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
                      (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
                      (12 12 (:TYPE-PRESCRIPTION ATOM-LISTP)))
(CONS-X-CDR-HONS-ASSOC-EQUAL
     (16 16
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (8 4
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(LOOKUP-BDDIFY-EXTRACT-BOOL-ALIST
     (948 948
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (482 241
          (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (224 224 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (224 224 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (65 65
         (:TYPE-PRESCRIPTION BDDIFY-EXTRACT-BOOL-ALIST)))
(AIG-Q-COMPOSE-OF-AIG-RESTRICT-OF-BDDIFY-EXTRACT
     (196 196
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (180 18
          (:DEFINITION BDDIFY-EXTRACT-BOOL-ALIST))
     (124 31 (:DEFINITION Q-NOT))
     (120 120
          (:TYPE-PRESCRIPTION ABS-BDD-AL-OKP-HONS-ASSOC-EQUAL-CONSP))
     (61 61 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (61 61 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (42 21
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (31 31 (:DEFINITION HONS))
     (28 28 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (28 28 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (18 18 (:DEFINITION HONS-ACONS!))
     (16 4
         (:REWRITE BDD-IMPL-NIL-IS-BDD-EQUIV-NIL))
     (9 3 (:REWRITE Q-NOT-UNDER-IFF))
     (9 3 (:DEFINITION HONS-EQUAL))
     (8 2 (:REWRITE BDD-IMPL-T-IS-BDD-EQUIV-T)))
(AIG-Q-COMPOSE-LIST-OF-AIG-RESTRICT-LIST-OF-BDDIFY-EXTRACT
     (438 9 (:DEFINITION AIG-Q-COMPOSE))
     (305 36 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (215 47 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (140 54 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (133 133
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (106 36 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (84 4 (:DEFINITION AIG-RESTRICT))
     (82 82
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (74 74 (:TYPE-PRESCRIPTION BOOLEANP))
     (72 72
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (50 5
         (:DEFINITION BDDIFY-EXTRACT-BOOL-ALIST))
     (42 42
         (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (42 18 (:DEFINITION HONS-GET))
     (36 9 (:DEFINITION Q-NOT))
     (27 9 (:DEFINITION AIG-ALIST-LOOKUP))
     (24 4
         (:REWRITE LOOKUP-BDDIFY-EXTRACT-BOOL-ALIST))
     (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (10 5
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (9 9 (:DEFINITION HONS))
     (8 2
        (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (5 5 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (5 5 (:REWRITE BDD-IMPL-TRANSITIVE-1))
     (5 5 (:DEFINITION HONS-ACONS!))
     (5 2
        (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV)))
(BDD-AL-MAX-DEPTH-<=-AL-MAX-DEPTH
     (12 12
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
     (2 2
        (:LINEAR MAX-DEPTH-WHEN-BDD-EQUIV-AIG-Q-COMPOSE)))
(AIG-BDDIFY-LIST-OK (488 8 (:DEFINITION AIG-Q-COMPOSE-LIST))
                    (376 8 (:DEFINITION AIG-Q-COMPOSE))
                    (256 32 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
                    (188 44 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                    (128 48 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                    (124 124
                         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                    (96 32 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
                    (94 94
                        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                    (84 4 (:DEFINITION AIG-RESTRICT-LIST))
                    (80 8
                        (:DEFINITION BDDIFY-EXTRACT-BOOL-ALIST))
                    (72 72
                        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                    (72 4 (:DEFINITION AIG-RESTRICT))
                    (68 68 (:TYPE-PRESCRIPTION BOOLEANP))
                    (36 20 (:DEFINITION HONS-GET))
                    (32 32
                        (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
                    (32 8 (:DEFINITION Q-NOT))
                    (32 2 (:DEFINITION BDD-EQUIV-LIST))
                    (24 8 (:DEFINITION AIG-ALIST-LOOKUP))
                    (16 8
                        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                    (16 4
                        (:REWRITE LOOKUP-BDDIFY-EXTRACT-BOOL-ALIST))
                    (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
                    (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
                    (10 2
                        (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
                    (8 8 (:TYPE-PRESCRIPTION ATOM-LISTP))
                    (8 8 (:DEFINITION HONS-ACONS!))
                    (8 8 (:DEFINITION HONS))
                    (4 4 (:TYPE-PRESCRIPTION BDD-IMPL))
                    (2 2 (:REWRITE BDD-IMPL-TRANSITIVE-2))
                    (2 2 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(AIG-BDDIFY-LIST-X-WEAKENING-TRUE-LISTP
     (48 8
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (36 4 (:DEFINITION TRUE-LISTP))
     (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (16 16
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (8 8 (:REWRITE SET::IN-SET))
     (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(AIG-BDDIFY-LIST-VAR-WEAKENING-TRUE-LISTP
     (48 8
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (36 4 (:DEFINITION TRUE-LISTP))
     (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (16 16
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (8 8 (:REWRITE SET::IN-SET))
     (3 3
        (:REWRITE AIG-BDDIFY-VAR-WEAKENING-OK)))
(AIG-BDDIFY-LIST-ITER1-TRUE-LISTP
     (72 12
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (54 6 (:DEFINITION TRUE-LISTP))
     (42 42
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (24 24 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (24 12 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (22 22 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (22 22 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (12 12 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (12 12 (:REWRITE SET::IN-SET)))
(AIG-BDDIFY-LIST-TRUE-LISTP
     (21 1 (:DEFINITION AIG-RESTRICT-LIST))
     (18 1 (:DEFINITION AIG-RESTRICT))
     (10 1
         (:DEFINITION BDDIFY-EXTRACT-BOOL-ALIST))
     (8 8
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (8 2 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (6 2 (:DEFINITION HONS-GET))
     (5 5 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (5 1 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (4 1
        (:REWRITE LOOKUP-BDDIFY-EXTRACT-BOOL-ALIST))
     (3 3 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (2 1
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
     (1 1 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (1 1 (:DEFINITION HONS-ACONS!)))
(VARS-TO-BDD-BINDINGS)
(AIG-BDDIFY-SAT)
(BDD-EQUIV-LIST-IMPLIES-BDD-EQUIV-CAR-1
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (1 1 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (1 1 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(BDD-EQUIV-LIST-IMPLIES-BDD-EQUIV-LIST-CDR-1
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (5 1
        (:REWRITE BDD-EQUIV-WHEN-BOTH-IMPLICATIONS))
     (2 2 (:TYPE-PRESCRIPTION BDD-IMPL))
     (1 1 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (1 1 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(BDD-EQUIV-IMPLIES-BDD-EQUIV-LIST-CONS-1
     (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(BDD-EQUIV-LIST-IMPLIES-BDD-EQUIV-LIST-CONS-2
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-2))
     (3 3 (:REWRITE BDD-IMPL-TRANSITIVE-1)))
(UBDDP-VAL-ALISTP-VARS-TO-BDD-BINDINGS
     (28 28
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
     (6 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(HONS-ASSOC-EQUAL-VARS-TO-BDD-BINDINGS
     (350 350
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (108 12 (:REWRITE SUBSETP-CAR-MEMBER))
     (80 64 (:REWRITE SUBSETP-MEMBER . 3))
     (73 73 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (73 73 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (64 64 (:REWRITE SUBSETP-MEMBER . 4))
     (64 64 (:REWRITE INTERSECTP-MEMBER . 3))
     (64 64 (:REWRITE INTERSECTP-MEMBER . 2))
     (48 24 (:REWRITE DEFAULT-UNARY-MINUS))
     (42 14 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (37 37 (:META CANCEL_PLUS-LESSP-CORRECT))
     (37 18
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (31 31 (:REWRITE SUBSETP-MEMBER . 2))
     (31 31 (:REWRITE SUBSETP-MEMBER . 1))
     (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (14 14 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (14 14 (:REWRITE SUBSETP-TRANS2))
     (14 14 (:REWRITE SUBSETP-TRANS))
     (4 4 (:TYPE-PRESCRIPTION HONS-ACONS)))
(VARS-TO-BDD-ENV)
(NTH-VARS-TO-BDD-ENV (780 59 (:REWRITE NTH-LEN-LST))
                     (214 214
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (166 166 (:META CANCEL_PLUS-LESSP-CORRECT))
                     (95 95
                         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                     (63 63
                         (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
                     (17 17 (:REWRITE ZP-OPEN))
                     (15 15 (:META CANCEL_TIMES-EQUAL-CORRECT))
                     (15 15 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(LEN-MEMBER-EQUAL (108 108
                       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                  (53 37 (:REWRITE SUBSETP-MEMBER . 3))
                  (37 37 (:REWRITE SUBSETP-MEMBER . 4))
                  (37 37 (:REWRITE INTERSECTP-MEMBER . 3))
                  (37 37 (:REWRITE INTERSECTP-MEMBER . 2))
                  (21 21 (:META CANCEL_TIMES-EQUAL-CORRECT))
                  (21 21 (:META CANCEL_PLUS-EQUAL-CORRECT))
                  (18 2 (:REWRITE SUBSETP-CAR-MEMBER))
                  (15 15 (:REWRITE SUBSETP-MEMBER . 2))
                  (15 15 (:REWRITE SUBSETP-MEMBER . 1))
                  (14 14
                      (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
                  (12 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
                  (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                  (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
                  (4 4 (:REWRITE SUBSETP-TRANS2))
                  (4 4 (:REWRITE SUBSETP-TRANS)))
(NTH-OF-INDEX (572 14 (:REWRITE NTH-LEN-LST))
              (124 12 (:DEFINITION NFIX))
              (102 102
                   (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
              (49 49 (:META CANCEL_PLUS-LESSP-CORRECT))
              (48 32 (:REWRITE SUBSETP-MEMBER . 3))
              (40 16
                  (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
              (32 32 (:REWRITE SUBSETP-MEMBER . 4))
              (32 32 (:REWRITE INTERSECTP-MEMBER . 3))
              (32 32 (:REWRITE INTERSECTP-MEMBER . 2))
              (24 24 (:META CANCEL_TIMES-EQUAL-CORRECT))
              (24 24 (:META CANCEL_PLUS-EQUAL-CORRECT))
              (20 10 (:REWRITE DEFAULT-UNARY-MINUS))
              (18 2 (:REWRITE SUBSETP-CAR-MEMBER))
              (16 16
                  (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
              (12 6 (:REWRITE <-+-NEGATIVE-0-2))
              (12 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
              (10 5 (:REWRITE <-0-+-NEGATIVE-2))
              (10 5 (:REWRITE <-+-NEGATIVE-0-1))
              (9 9 (:REWRITE SUBSETP-MEMBER . 2))
              (9 9 (:REWRITE SUBSETP-MEMBER . 1))
              (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
              (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
              (4 4 (:REWRITE SUBSETP-TRANS2))
              (4 4 (:REWRITE SUBSETP-TRANS)))
(IDX-REWRITE (62 5 (:DEFINITION MEMBER-EQUAL))
             (38 38
                 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
             (30 10 (:REWRITE MEMBER-WHEN-ATOM))
             (10 10 (:REWRITE SUBSETP-MEMBER . 4))
             (10 10 (:REWRITE SUBSETP-MEMBER . 3))
             (10 10 (:REWRITE INTERSECTP-MEMBER . 3))
             (10 10 (:REWRITE INTERSECTP-MEMBER . 2))
             (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
             (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
             (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
             (2 2 (:REWRITE SUBSETP-MEMBER . 2))
             (2 2 (:REWRITE SUBSETP-MEMBER . 1))
             (2 2
                (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
             (2 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(AIG-Q-COMPOSE-VARS-TO-BDD-ENV
     (4546 10 (:DEFINITION AIG-Q-COMPOSE))
     (4292 234 (:REWRITE SUBSETP-CAR-MEMBER))
     (2458 272 (:REWRITE SUBSETP-MEMBER . 2))
     (2306 270 (:REWRITE SUBSETP-TRANS2))
     (2258 134 (:DEFINITION MEMBER-EQUAL))
     (1518 1518
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (802 62 (:DEFINITION BINARY-APPEND))
     (784 254 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (612 102
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (566 132 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (552 106
          (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (474 230 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (272 272 (:REWRITE SUBSETP-MEMBER . 1))
     (270 90 (:REWRITE SET::SFIX-WHEN-EMPTY))
     (268 268 (:REWRITE SUBSETP-TRANS))
     (228 76 (:REWRITE MEMBER-WHEN-ATOM))
     (196 196 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (196 196 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (180 180
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (164 20 (:REWRITE MEMBER-OF-CONS))
     (164 10 (:REWRITE EVAL-BDD-DEPTH))
     (148 24 (:REWRITE SUBSETP-CONS-2))
     (80 80 (:TYPE-PRESCRIPTION BOOLEANP))
     (76 76 (:REWRITE SUBSETP-MEMBER . 4))
     (76 76 (:REWRITE SUBSETP-MEMBER . 3))
     (76 76 (:REWRITE INTERSECTP-MEMBER . 3))
     (76 76 (:REWRITE INTERSECTP-MEMBER . 2))
     (75 11
         (:REWRITE BDD-MAX-DEPTH-AIG-Q-COMPOSE))
     (60 28 (:DEFINITION LEN))
     (55 55 (:TYPE-PRESCRIPTION CONS-MAKE-LIST))
     (55 11 (:DEFINITION VARS-TO-BDD-ENV))
     (55 11 (:DEFINITION VARS-TO-BDD-BINDINGS))
     (54 54 (:TYPE-PRESCRIPTION MAX-DEPTH))
     (52 52 (:META CANCEL_PLUS-LESSP-CORRECT))
     (44 11 (:DEFINITION Q-NOT))
     (40 2 (:REWRITE BDD-MAX-DEPTH-Q-AND-BOUND))
     (37 9 (:LINEAR MAX-DEPTH-GTE-BDD-MAX-DEPTH))
     (32 32
         (:TYPE-PRESCRIPTION BDD-AL-MAX-DEPTH))
     (32 16
         (:REWRITE COMMUTATIVITY-OF-APPEND-UNDER-SET-EQUIV))
     (24 8
         (:REWRITE APPEND-OF-CONS-UNDER-SET-EQUIV))
     (24 8 (:DEFINITION ATOM))
     (24 1 (:REWRITE NTH-LEN-LST))
     (20 10 (:REWRITE DEFAULT-UNARY-MINUS))
     (14 14 (:REWRITE FOLD-CONSTS-IN-+))
     (14 14
         (:LINEAR MAX-DEPTH-WHEN-BDD-EQUIV-AIG-Q-COMPOSE))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (12 6
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (11 11
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (11 11
         (:LINEAR BDD-MAX-DEPTH-AIG-Q-COMPOSE))
     (11 11 (:DEFINITION LNFIX$INLINE))
     (11 11 (:DEFINITION HONS-ACONS))
     (11 11 (:DEFINITION HONS))
     (11 1 (:REWRITE LEN-APPEND))
     (10 1
         (:REWRITE |(qs-subset x (q-and x y))|))
     (8 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (3 3
        (:LINEAR ABS-MEMO-OKP-HONS-ASSOC-EQUAL-LINEAR))
     (2 2 (:TYPE-PRESCRIPTION VARS-TO-BDD-ENV))
     (2 2 (:REWRITE BDD-MAX-DEPTH-Q-NOT))
     (2 2 (:LINEAR BDD-MAX-DEPTH-Q-AND-BOUND)))
(AIG-BDDIFY-SAT-CORRECT-FOR-UNSAT
     (301 14 (:DEFINITION AIG-VARS))
     (244 4 (:DEFINITION AIG-Q-COMPOSE))
     (164 58 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (149 33 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (128 16 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (95 95
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (80 4 (:DEFINITION AIG-ALIST-LOOKUP))
     (74 74
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (70 14 (:REWRITE SET::INSERT-IDENTITY))
     (68 4
         (:REWRITE HONS-ASSOC-EQUAL-VARS-TO-BDD-BINDINGS))
     (60 10 (:DEFINITION VARS-TO-BDD-BINDINGS))
     (56 56 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (48 16 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (48 4 (:DEFINITION MEMBER-EQUAL))
     (44 44
         (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
     (42 42 (:TYPE-PRESCRIPTION SET::IN-TYPE))
     (42 14 (:REWRITE SET::UNION-EMPTY-Y))
     (42 14 (:REWRITE SET::UNION-EMPTY-X))
     (36 36
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
     (28 14 (:REWRITE SET::IN-TAIL))
     (28 4
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (28 4 (:DEFINITION VARS-TO-BDD-ENV))
     (27 27 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (27 27 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (20 20 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (16 4
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (16 4 (:DEFINITION Q-NOT))
     (14 14 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (10 10 (:DEFINITION HONS-ACONS))
     (10 8
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (8 8 (:REWRITE SUBSETP-MEMBER . 2))
     (8 8 (:REWRITE SUBSETP-MEMBER . 1))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:DEFINITION HONS)))
