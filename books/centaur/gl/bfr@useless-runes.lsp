(GL::BFR-MODE)
(GL::BFR-AIG)
(GL::BFR-BDD)
(BFR-EVAL (36 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
          (16 4 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
          (14 2 (:DEFINITION AIG-ENV-LOOKUP))
          (12 12
              (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
          (10 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
          (9 9 (:TYPE-PRESCRIPTION BOOLEANP))
          (8 2 (:DEFINITION HONS-GET))
          (6 6 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
          (6 6 (:REWRITE DEFAULT-CDR))
          (6 2 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
          (6 2 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
          (6 2
             (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
          (4 4
             (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
          (4 4 (:REWRITE DEFAULT-CAR))
          (2 2 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
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
(GL::BFR-EVAL-CONSTS (6 2
                        (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                     (4 4
                        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                     (2 2
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                     (2 2
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                     (2 2
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                     (2 2
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1)))
(GL::BFR-EQUIV)
(GL::BFR-EQUIV-NECC)
(GL::BFR-EQUIV-REFL)
(GL::BFR-EQUIV-SYMM)
(GL::BFR-EQUIV-TRANS)
(GL::BFR-EQUIV-IS-AN-EQUIVALENCE)
(GL::BFR-EQUIV-IMPLIES-EQUAL-BFR-EVAL-1)
(GL::AIG-VAR-FIX (1 1 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX)))
(GL::AIG-VAR-P-OF-AIG-VAR-FIX (16 16 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
                              (16 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                              (10 2 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                              (6 6
                                 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE)))
(GL::AIG-VAR-FIX-WHEN-AIG-VAR-P (19 19 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
                                (16 3 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                                (6 2 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                                (4 4
                                   (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                                (4 1 (:DEFINITION BOOLEANP))
                                (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                                (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
                                (1 1 (:DEFINITION IFF)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT (53 53 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
                                (21 7 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                                (16 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                                (10 1 (:DEFINITION BOOLEANP))
                                (9 3 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                                (7 7
                                   (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                                (4 4 (:TYPE-PRESCRIPTION BOOLEANP)))
(GL::AIG-VAR-EQUIV$INLINE (4 4 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX)))
(GL::AIG-VAR-EQUIV-IS-AN-EQUIVALENCE)
(GL::AIG-VAR-EQUIV-IMPLIES-EQUAL-AIG-VAR-FIX-1)
(GL::AIG-VAR-FIX-UNDER-AIG-VAR-EQUIV)
(GL::BFR-VARNAME-P)
(GL::BFR-VARNAME-FIX (1 1
                        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX)))
(GL::BFR-VARNAME-P-OF-BFR-VARNAME-FIX
     (3 3
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (2 2 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX)))
(GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P
     (8 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (5 1 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (3 3
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (3 3
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (1 1 (:REWRITE NFIX-WHEN-NOT-NATP))
     (1 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT (43 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                                (28 1 (:DEFINITION BOOLEANP))
                                (24 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                                (20 6 (:REWRITE NFIX-WHEN-NOT-NATP))
                                (12 12 (:TYPE-PRESCRIPTION NATP))
                                (12 6 (:REWRITE NATP-WHEN-GTE-0))
                                (9 9
                                   (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
                                (9 4 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                                (8 8
                                   (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                                (6 6 (:REWRITE NATP-WHEN-INTEGERP))
                                (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                                (3 3 (:REWRITE DEFAULT-<-2))
                                (3 3 (:REWRITE DEFAULT-<-1)))
(GL::BFR-VARNAME-EQUIV$INLINE (4 4
                                 (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX)))
(GL::BFR-VARNAME-EQUIV-IS-AN-EQUIVALENCE)
(GL::BFR-VARNAME-EQUIV-IMPLIES-EQUAL-BFR-VARNAME-FIX-1)
(GL::BFR-VARNAME-FIX-UNDER-BFR-VARNAME-EQUIV)
(GL::NFIX-OF-BFR-VARNAME-FIX (34 1 (:REWRITE NFIX-EQUAL-TO-NONZERO))
                             (18 5 (:REWRITE ZP-WHEN-INTEGERP))
                             (18 5 (:REWRITE ZP-WHEN-GT-0))
                             (16 2 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
                             (14 2 (:REWRITE NFIX-WHEN-NATP))
                             (10 2 (:REWRITE NFIX-WHEN-NOT-NATP))
                             (8 8 (:TYPE-PRESCRIPTION NATP))
                             (8 4 (:REWRITE NATP-WHEN-GTE-0))
                             (8 1
                                (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
                             (6 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                             (4 4 (:TYPE-PRESCRIPTION ZP))
                             (4 4 (:REWRITE ZP-OPEN))
                             (4 4 (:REWRITE NATP-WHEN-INTEGERP))
                             (3 3 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                             (3 3 (:REWRITE DEFAULT-<-2))
                             (3 3 (:REWRITE DEFAULT-<-1))
                             (2 2
                                (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                             (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
                             (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                             (2 1 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                             (1 1
                                (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST)))
(GL::BFR-VARNAME-FIX-OF-NFIX (9 4 (:REWRITE NFIX-WHEN-NOT-NATP))
                             (4 4 (:TYPE-PRESCRIPTION NATP))
                             (4 2 (:REWRITE NATP-WHEN-GTE-0))
                             (2 2 (:REWRITE NATP-WHEN-INTEGERP))
                             (1 1 (:REWRITE DEFAULT-<-2))
                             (1 1 (:REWRITE DEFAULT-<-1)))
(GL::BFR-VARNAME-P-WHEN-NATP)
(GL::BFR-LOOKUP)
(GL::BFR-VARNAME-EQUIV-IMPLIES-EQUAL-BFR-LOOKUP-1
     (114 114
          (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (54 2 (:DEFINITION NTH))
     (40 4
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (28 4
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (16 2 (:REWRITE ZP-WHEN-GT-0))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (12 2 (:REWRITE ZP-OPEN))
     (12 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (10 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (8 2 (:REWRITE ZP-WHEN-INTEGERP))
     (8 1 (:DEFINITION BOOLEANP))
     (6 2 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (4 4 (:REWRITE NATP-WHEN-INTEGERP))
     (4 4 (:REWRITE DEFAULT-CDR))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1)))
(GL::BFR-SET-VAR (20 10
                     (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
                 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(GL::BFR-LOOKUP-BFR-SET-VAR
     (616 616
          (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (378 49
          (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
     (238 7 (:REWRITE NFIX-EQUAL-TO-NONZERO))
     (235 47 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (183 39 (:REWRITE NFIX-WHEN-NOT-NATP))
     (141 141
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (140 140 (:TYPE-PRESCRIPTION NATP))
     (140 70 (:REWRITE NATP-WHEN-GTE-0))
     (134 134
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (126 35 (:REWRITE ZP-WHEN-INTEGERP))
     (126 35 (:REWRITE ZP-WHEN-GT-0))
     (112 14 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
     (94 94
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (94 47 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (88 10 (:DEFINITION BOOLEANP))
     (70 70 (:REWRITE NATP-WHEN-INTEGERP))
     (42 42 (:REWRITE DEFAULT-<-2))
     (42 42 (:REWRITE DEFAULT-<-1))
     (31 11
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (28 28 (:TYPE-PRESCRIPTION ZP))
     (28 28 (:REWRITE ZP-OPEN))
     (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
     (20 20
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (14 14
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (10 10 (:REWRITE DEFAULT-CAR))
     (9 9 (:REWRITE DEFAULT-CDR))
     (7 7
        (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
     (6 6
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX)))
(GL::BFR-VARNAME-EQUIV-IMPLIES-EQUAL-BFR-SET-VAR-1
     (146 146
          (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (128 4 (:DEFINITION UPDATE-NTH))
     (64 64
         (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (40 4
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (32 4 (:REWRITE ZP-WHEN-GT-0))
     (28 4
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (24 24
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (24 8 (:REWRITE DEFAULT-CDR))
     (24 4 (:REWRITE ZP-OPEN))
     (16 12 (:REWRITE DEFAULT-<-2))
     (16 4 (:REWRITE ZP-WHEN-INTEGERP))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (12 4 (:REWRITE DEFAULT-CAR))
     (12 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (8 1 (:DEFINITION BOOLEANP))
     (4 4 (:REWRITE NATP-WHEN-INTEGERP))
     (4 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP)))
(GL::BFR-VAR (1 1 (:TYPE-PRESCRIPTION GL::BFR-VAR)))
(GL::BFR-EVAL-BFR-VAR (130 130
                           (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
                      (112 14
                           (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
                      (83 15 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                      (54 15 (:REWRITE ZP-WHEN-GT-0))
                      (51 1 (:DEFINITION EVAL-BDD))
                      (40 40
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (35 5 (:REWRITE NFIX-WHEN-NATP))
                      (32 12
                          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                      (30 30
                          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                      (30 16 (:REWRITE DEFAULT-CDR))
                      (30 4 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                      (29 3 (:DEFINITION BOOLEANP))
                      (25 25 (:TYPE-PRESCRIPTION QV))
                      (25 5 (:REWRITE NFIX-WHEN-NOT-NATP))
                      (20 20 (:TYPE-PRESCRIPTION NATP))
                      (20 10 (:REWRITE NATP-WHEN-GTE-0))
                      (12 12 (:REWRITE ZP-OPEN))
                      (10 10 (:REWRITE NATP-WHEN-INTEGERP))
                      (10 2 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
                      (10 1 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
                      (8 8 (:REWRITE DEFAULT-<-2))
                      (8 8 (:REWRITE DEFAULT-<-1))
                      (7 7 (:REWRITE DEFAULT-CAR))
                      (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
                      (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
                      (6 4
                         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                      (6 3 (:REWRITE DEFAULT-+-2))
                      (4 4
                         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                      (4 4
                         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                      (4 4
                         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                      (4 4
                         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                      (4 1
                         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
                      (3 3 (:REWRITE DEFAULT-+-1))
                      (3 1
                         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                      (2 2
                         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
                      (2 2 (:TYPE-PRESCRIPTION ALISTP))
                      (2 2 (:TYPE-PRESCRIPTION AIG-EVAL))
                      (2 1
                         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
                      (1 1
                         (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
                      (1 1 (:REWRITE ALISTP-WHEN-ATOM)))
(GL::BFR-VARNAME-EQUIV-IMPLIES-EQUAL-BFR-VAR-1
     (90 90
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (40 4
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (28 4
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (12 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (8 1 (:DEFINITION BOOLEANP))
     (6 6 (:TYPE-PRESCRIPTION GL::BFR-VAR))
     (4 4 (:REWRITE NATP-WHEN-INTEGERP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2 (:TYPE-PRESCRIPTION BOOLEANP)))
(BFR-NOT (20 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
         (12 2 (:DEFINITION Q-NOT))
         (7 7 (:TYPE-PRESCRIPTION BOOLEANP))
         (4 4
            (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
         (2 2 (:REWRITE DEFAULT-CDR))
         (2 2 (:REWRITE DEFAULT-CAR))
         (2 2 (:DEFINITION HONS)))
(GL::BFR-EVAL-BFR-NOT (32 8 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                      (24 7 (:DEFINITION BOOLEANP))
                      (22 22
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (21 4 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                      (20 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                      (18 3 (:DEFINITION Q-NOT))
                      (15 15 (:REWRITE DEFAULT-CDR))
                      (13 13 (:TYPE-PRESCRIPTION BOOLEANP))
                      (12 12
                          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                      (12 4 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                      (11 11 (:REWRITE DEFAULT-CAR))
                      (9 9 (:TYPE-PRESCRIPTION Q-NOT))
                      (9 2 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                      (8 8
                         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                      (6 2
                         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                      (5 5
                         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                      (4 4
                         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                      (4 4
                         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                      (4 4
                         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                      (3 3 (:DEFINITION HONS))
                      (3 2
                         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                      (2 1 (:REWRITE EQUAL-T-AND-Q-NOT)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-NOT-1)
(GL::BFR-BINARY-AND (30 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                    (20 3 (:DEFINITION BOOLEANP))
                    (10 10 (:TYPE-PRESCRIPTION BOOLEANP)))
(GL::BFR-EVAL-BFR-BINARY-AND
     (80 20 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (50 15 (:DEFINITION BOOLEANP))
     (50 10 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (44 44
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (34 7 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (30 30 (:TYPE-PRESCRIPTION BOOLEANP))
     (30 30
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (30 30 (:REWRITE DEFAULT-CDR))
     (30 10
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (21 6 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (20 20
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (20 20 (:REWRITE DEFAULT-CAR))
     (18 6
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (11 11 (:TYPE-PRESCRIPTION Q-BINARY-AND))
     (10 10
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (8 8
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (7 7
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (7 7
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (7 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:TYPE-PRESCRIPTION UBDDP))
     (3 1
        (:REWRITE |(qs-subset x (q-and x y))|))
     (3 1
        (:REWRITE |(qs-subset (q-and x y) x)|)))
(GL::BFR-AND-OF-NIL)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-BINARY-AND-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-BINARY-AND-2)
(GL::BFR-AND-MACRO-LOGIC-PART)
(GL::BFR-AND-MACRO-EXEC-PART)
(BFR-ITE-FN (430 2 (:DEFINITION Q-ITE-FN))
            (204 6 (:DEFINITION QCONS$INLINE))
            (200 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
            (102 14 (:REWRITE |(q-ite non-nil y z)|))
            (64 64
                (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
            (48 6 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
            (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
            (32 8 (:DEFINITION QCDR$INLINE))
            (32 8 (:DEFINITION QCAR$INLINE))
            (24 6
                (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
            (20 20 (:DEFINITION HONS))
            (20 6 (:DEFINITION HONS-EQUAL))
            (16 16 (:REWRITE DEFAULT-CDR))
            (16 16 (:REWRITE DEFAULT-CAR))
            (12 12
                (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
            (12 12 (:TYPE-PRESCRIPTION ALISTP))
            (12 6
                (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
            (8 2 (:DEFINITION Q-NOT))
            (6 6 (:TYPE-PRESCRIPTION ATOM-LISTP))
            (6 6
               (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
            (6 6 (:REWRITE ALISTP-WHEN-ATOM)))
(GL::BFR-EVAL-BFR-ITE-FN
     (645 3 (:DEFINITION Q-ITE-FN))
     (306 9 (:DEFINITION QCONS$INLINE))
     (261 54 (:DEFINITION BOOLEANP))
     (191 191 (:TYPE-PRESCRIPTION Q-ITE-FN))
     (168 168
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (160 40 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (153 21 (:REWRITE |(q-ite non-nil y z)|))
     (110 110 (:TYPE-PRESCRIPTION BOOLEANP))
     (100 20 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (84 84 (:REWRITE DEFAULT-CDR))
     (72 9 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (64 64 (:REWRITE DEFAULT-CAR))
     (60 60
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (60 20
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (50 11 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (48 12 (:DEFINITION QCDR$INLINE))
     (48 12 (:DEFINITION QCAR$INLINE))
     (40 40
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (36 9
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (30 30 (:DEFINITION HONS))
     (30 9 (:DEFINITION HONS-EQUAL))
     (27 8 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (24 8
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (18 18
         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (18 18 (:TYPE-PRESCRIPTION ALISTP))
     (18 9
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (13 13
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (12 3 (:DEFINITION Q-NOT))
     (11 11
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (11 11
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (10 10
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 9 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (9 9
        (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (9 9 (:REWRITE ALISTP-WHEN-ATOM))
     (9 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4 (:TYPE-PRESCRIPTION UBDDP))
     (3 1 (:REWRITE QS-SUBSET-OF-Q-ITE-RIGHT))
     (3 1 (:REWRITE QS-SUBSET-OF-Q-ITE-LEFT)))
(GL::BFR-ITE-FN-BOOLS)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ITE-FN-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ITE-FN-2)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ITE-FN-3)
(GL::BFR-BINARY-OR (42 10
                       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE)))
(GL::BFR-EVAL-BFR-BINARY-OR
     (117 32 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (96 24 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (87 19 (:DEFINITION BOOLEANP))
     (60 12 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (56 56
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (40 40 (:TYPE-PRESCRIPTION BOOLEANP))
     (39 8 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (36 36
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (36 36 (:REWRITE DEFAULT-CDR))
     (36 12
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (27 8 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (24 24
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (24 24 (:REWRITE DEFAULT-CAR))
     (24 8
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (13 13
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (11 11 (:TYPE-PRESCRIPTION Q-BINARY-OR))
     (10 10
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 8
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (8 8
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (8 8
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (4 4 (:TYPE-PRESCRIPTION UBDDP))
     (3 1 (:REWRITE |(qs-subset x (q-or x y))|))
     (3 1
        (:REWRITE |(qs-subset (q-or x y) x)|)))
(GL::BFR-OR-OF-T)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-BINARY-OR-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-BINARY-OR-2)
(GL::BFR-OR-MACRO-LOGIC-PART)
(GL::BFR-OR-MACRO-EXEC-PART)
(BFR-XOR (24 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
         (10 10 (:TYPE-PRESCRIPTION BOOLEANP)))
(GL::BFR-EVAL-BFR-XOR (324 12 (:DEFINITION AIG-EVAL))
                      (96 24 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                      (84 12 (:DEFINITION AIG-ENV-LOOKUP))
                      (68 68
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (60 12 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                      (48 16 (:DEFINITION BOOLEANP))
                      (48 12 (:DEFINITION HONS-GET))
                      (40 13
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                      (39 12 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                      (36 36
                          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                      (36 36 (:REWRITE DEFAULT-CDR))
                      (36 12
                          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                      (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
                      (32 12
                          (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                      (24 24
                          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                      (24 24 (:REWRITE DEFAULT-CAR))
                      (22 13
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                      (20 4 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                      (13 13
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                      (13 13
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                      (13 12
                          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                      (12 12
                          (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
                      (8 8 (:TYPE-PRESCRIPTION QS-SUBSET))
                      (4 4 (:TYPE-PRESCRIPTION Q-BINARY-XOR))
                      (4 4
                         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                      (4 4
                         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-XOR-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-XOR-2)
(BFR-IFF (24 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
         (10 10 (:TYPE-PRESCRIPTION BOOLEANP)))
(GL::BFR-EVAL-BFR-IFF (144 36 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                      (103 31 (:DEFINITION BOOLEANP))
                      (90 18 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                      (85 19 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                      (76 76
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (62 62 (:TYPE-PRESCRIPTION BOOLEANP))
                      (54 54
                          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                      (54 54 (:REWRITE DEFAULT-CDR))
                      (54 18
                          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                      (36 36
                          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                      (36 36 (:REWRITE DEFAULT-CAR))
                      (34 11 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                      (31 11
                          (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                      (19 19
                          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                      (19 19
                          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                      (18 18 (:TYPE-PRESCRIPTION Q-BINARY-IFF))
                      (17 17
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                      (14 14
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                      (12 11
                          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-IFF-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-IFF-2)
(GL::BFR-NOR (56 16 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
             (16 2 (:DEFINITION Q-NOT))
             (4 4
                (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
             (2 2 (:REWRITE DEFAULT-CDR))
             (2 2 (:REWRITE DEFAULT-CAR))
             (2 2 (:DEFINITION HONS)))
(GL::BFR-EVAL-BFR-NOR (64 16 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                      (58 15 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                      (56 15 (:DEFINITION BOOLEANP))
                      (40 40
                          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (40 8 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                      (32 4 (:DEFINITION Q-NOT))
                      (29 29 (:TYPE-PRESCRIPTION BOOLEANP))
                      (28 28 (:REWRITE DEFAULT-CDR))
                      (24 24
                          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                      (24 8 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                      (20 20 (:REWRITE DEFAULT-CAR))
                      (18 18 (:TYPE-PRESCRIPTION Q-BINARY-OR))
                      (16 16
                          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                      (15 15
                          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                      (15 15
                          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                      (15 4 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                      (12 12
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                      (12 4
                          (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                      (10 10
                          (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                      (9 9 (:TYPE-PRESCRIPTION Q-NOT))
                      (8 8 (:TYPE-PRESCRIPTION UBDDP))
                      (5 4
                         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                      (4 4 (:DEFINITION HONS))
                      (4 1 (:REWRITE EQUAL-T-AND-Q-NOT))
                      (3 1 (:REWRITE |(qs-subset y (q-or x y))|))
                      (3 1 (:REWRITE |(qs-subset x (q-or x y))|))
                      (3 1 (:REWRITE |(qs-subset (q-or x y) y)|))
                      (3 1
                         (:REWRITE |(qs-subset (q-or x y) x)|)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-NOR-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-NOR-2)
(GL::BFR-NAND (37 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
              (16 2 (:DEFINITION Q-NOT))
              (4 4
                 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
              (2 2 (:REWRITE DEFAULT-CDR))
              (2 2 (:REWRITE DEFAULT-CAR))
              (2 2 (:DEFINITION HONS)))
(GL::BFR-EVAL-BFR-NAND (80 14 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                       (73 17 (:DEFINITION BOOLEANP))
                       (64 16 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                       (40 40
                           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                       (40 8 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                       (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
                       (32 4 (:DEFINITION Q-NOT))
                       (28 28 (:TYPE-PRESCRIPTION Q-BINARY-AND))
                       (28 28 (:REWRITE DEFAULT-CDR))
                       (24 24
                           (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                       (24 8 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                       (20 20 (:REWRITE DEFAULT-CAR))
                       (16 16
                           (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                       (15 4 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                       (14 14 (:TYPE-PRESCRIPTION Q-NOT))
                       (14 14
                           (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                       (14 14
                           (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                       (12 12
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                       (12 4
                           (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                       (10 10
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                       (8 8 (:TYPE-PRESCRIPTION UBDDP))
                       (8 2 (:REWRITE EQUAL-T-AND-Q-NOT))
                       (5 4
                          (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                       (4 4 (:DEFINITION HONS))
                       (3 1
                          (:REWRITE |(qs-subset y (q-and x y))|))
                       (3 1
                          (:REWRITE |(qs-subset x (q-and x y))|))
                       (3 1
                          (:REWRITE |(qs-subset (q-and x y) y)|))
                       (3 1
                          (:REWRITE |(qs-subset (q-and x y) x)|)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-NAND-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-NAND-2)
(GL::BFR-ANDC1 (56 16
                   (:REWRITE EQUAL-OF-BOOLEANS-REWRITE)))
(GL::BFR-EVAL-BFR-ANDC1 (80 20 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                        (53 16 (:DEFINITION BOOLEANP))
                        (50 10 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                        (44 44
                            (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                        (39 8 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                        (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
                        (30 30
                            (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                        (30 30 (:REWRITE DEFAULT-CDR))
                        (30 10
                            (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                        (21 6 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                        (20 20
                            (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                        (20 20 (:REWRITE DEFAULT-CAR))
                        (18 6
                            (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                        (11 11 (:TYPE-PRESCRIPTION Q-AND-C1-FN))
                        (10 10
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                        (8 8
                           (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                        (8 8
                           (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                        (8 8
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                        (7 6
                           (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ANDC1-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ANDC1-2)
(GL::BFR-ANDC2 (37 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE)))
(GL::BFR-EVAL-BFR-ANDC2 (96 24 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
                        (73 21 (:DEFINITION BOOLEANP))
                        (63 13 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                        (60 12 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
                        (56 56
                            (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                        (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
                        (36 36
                            (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
                        (36 36 (:REWRITE DEFAULT-CDR))
                        (36 12
                            (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                        (27 8 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                        (24 24
                            (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
                        (24 24 (:REWRITE DEFAULT-CAR))
                        (24 8
                            (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                        (18 18 (:TYPE-PRESCRIPTION Q-AND-C2-FN))
                        (13 13
                            (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                        (13 13
                            (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                        (13 13
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                        (11 11
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                        (9 8
                           (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ANDC2-1)
(GL::BFR-EQUIV-IMPLIES-BFR-EQUIV-BFR-ANDC2-2)
(GL::BFR-ENV-EQUIV)
(GL::BFR-ENV-EQUIV-NECC)
(GL::BFR-ENV-EQUIV-REFL)
(GL::BFR-ENV-EQUIV-SYMM)
(GL::BFR-ENV-EQUIV-TRANS)
(GL::BFR-ENV-EQUIV-IS-AN-EQUIVALENCE)
(GL::BFR-ENV-EQUIV-IMPLIES-EQUAL-BFR-LOOKUP-2)
(GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE
     (200 41 (:REWRITE ZP-WHEN-GT-0))
     (198 22 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
     (173 41 (:REWRITE ZP-WHEN-INTEGERP))
     (162 162
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (162 36 (:REWRITE NFIX-WHEN-NOT-NATP))
     (120 120 (:TYPE-PRESCRIPTION NATP))
     (120 60 (:REWRITE NATP-WHEN-GTE-0))
     (79 79 (:REWRITE DEFAULT-<-2))
     (79 79 (:REWRITE DEFAULT-<-1))
     (60 60 (:REWRITE NATP-WHEN-INTEGERP))
     (54 31 (:REWRITE DEFAULT-+-2))
     (31 31 (:REWRITE DEFAULT-+-1))
     (22 22
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (19 19 (:REWRITE DEFAULT-CAR)))
(GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR
     (6 6
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (3 3 (:REWRITE DEFAULT-CAR)))
(GL::EVAL-BDD-WHEN-BFR-ENV-EQUIV-IND)
(GL::EVAL-BDD-WHEN-BFR-ENV-EQUIV
     (312 64 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (258 258
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (123 13 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (86 18 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (74 74
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (66 66
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (62 26
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (60 15
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (51 17 (:DEFINITION BOOLEANP))
     (40 32 (:REWRITE DEFAULT-CAR))
     (40 5 (:REWRITE ALISTP-OF-CDR))
     (34 34 (:TYPE-PRESCRIPTION BOOLEANP))
     (30 30
         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (30 30 (:TYPE-PRESCRIPTION ALISTP))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (18 18
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (18 18
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (15 15
         (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (15 15 (:REWRITE ALISTP-WHEN-ATOM)))
(GL::AIG-EVAL-WHEN-BFR-ENV-EQUIV
     (127 45
          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (85 57 (:REWRITE DEFAULT-CDR))
     (82 82
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (70 16 (:DEFINITION BOOLEANP))
     (44 44
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (43 43 (:TYPE-PRESCRIPTION BOOLEANP))
     (22 22 (:REWRITE DEFAULT-CAR))
     (20 4 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
     (5 5
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY)))
(GL::BFR-ENV-EQUIV-IMPLIES-EQUAL-BFR-EVAL-2
     (120 30 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (81 27 (:DEFINITION BOOLEANP))
     (75 15 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (60 60
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (60 60
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (60 12 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (54 54 (:TYPE-PRESCRIPTION BOOLEANP))
     (45 45
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (45 45 (:REWRITE DEFAULT-CDR))
     (45 15
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (30 30
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (30 30 (:REWRITE DEFAULT-CAR))
     (27 9
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (21 9 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (15 15
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (12 12
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (12 12
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (9 9
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 9
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(GL::BFR-TO-PARAM-SPACE)
(GL::BFR-TO-PARAM-SPACE-WEAK)
(GL::BFR-FROM-PARAM-SPACE)
(GL::BFR-PARAM-ENV)
(GL::BFR-EVAL-TO-PARAM-SPACE
     (150 2
          (:DEFINITION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (93 3 (:DEFINITION AIG-RESTRICT))
     (93 3 (:DEFINITION AIG-EVAL))
     (70 2 (:REWRITE MAKE-FAL-IS-APPEND))
     (58 58
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (54 22 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (50 50
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (48 12 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (42 3 (:DEFINITION BINARY-APPEND))
     (39 1 (:DEFINITION TO-PARAM-SPACE))
     (36 12 (:DEFINITION BOOLEANP))
     (33 33 (:REWRITE DEFAULT-CDR))
     (33 6 (:DEFINITION HONS-GET))
     (30 6 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (27 6 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (27 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (26 26
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ASSIGNS-ALIST))
     (26 1 (:DEFINITION PARAM-ENV))
     (24 24 (:TYPE-PRESCRIPTION BOOLEANP))
     (24 24 (:REWRITE DEFAULT-CAR))
     (21 3
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (21 3 (:DEFINITION AIG-ENV-LOOKUP))
     (18 18
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (14 14
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (14 1 (:DEFINITION QCONS$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (12 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (12 2 (:REWRITE ALISTP-WHEN-ATOM))
     (12 2 (:DEFINITION HONS-EQUAL))
     (10 2 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (9 3 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (9 3
        (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (6 6 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (4 4 (:TYPE-PRESCRIPTION QS-SUBSET))
     (4 2
        (:DEFINITION FLUSH-HONS-GET-HASH-TABLE-LINK))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (3 3
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (3 3 (:DEFINITION HONS))
     (2 2 (:TYPE-PRESCRIPTION ALISTP))
     (2 2
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (2 2
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (2 2
        (:REWRITE ALISTP-AIG-EXTRACT-ASSIGNS-ALIST))
     (2 2 (:DEFINITION FAST-ALIST-FREE)))
(GL::BFR-EVAL-TO-PARAM-SPACE-WEAK
     (93 3 (:DEFINITION AIG-EVAL))
     (39 1 (:DEFINITION TO-PARAM-SPACE))
     (32 32
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (29 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (26 26
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (26 1 (:DEFINITION PARAM-ENV))
     (24 6 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (21 21 (:REWRITE DEFAULT-CDR))
     (21 7 (:DEFINITION BOOLEANP))
     (21 3
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (21 3 (:DEFINITION AIG-ENV-LOOKUP))
     (15 15 (:REWRITE DEFAULT-CAR))
     (15 3 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
     (14 1 (:DEFINITION QCONS$INLINE))
     (12 3 (:DEFINITION HONS-GET))
     (10 2 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (9 9 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (9 3 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (9 3 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (9 3
        (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (6 6
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (4 4 (:TYPE-PRESCRIPTION QS-SUBSET))
     (3 3 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (3 3
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (3 3 (:DEFINITION HONS))
     (2 2
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (2 2
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1)))
(GL::BFR-EVAL-FROM-PARAM-SPACE
     (93 3 (:DEFINITION AIG-EVAL))
     (76 1 (:DEFINITION FROM-PARAM-SPACE))
     (55 3 (:DEFINITION QCONS$INLINE))
     (52 2 (:DEFINITION PARAM-ENV))
     (51 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (40 40
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (33 6 (:DEFINITION BOOLEANP))
     (31 31
         (:TYPE-PRESCRIPTION FROM-PARAM-SPACE))
     (30 30
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (27 27 (:REWRITE DEFAULT-CDR))
     (24 6 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (21 3 (:DEFINITION AIG-ENV-LOOKUP))
     (18 18 (:REWRITE DEFAULT-CAR))
     (15 3 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 3 (:DEFINITION HONS-GET))
     (9 9 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (9 3 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (9 3 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (9 3
        (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (6 6
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (6 6 (:DEFINITION HONS))
     (3 3 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
     (3 3
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (3 3
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(GL::BDD-MODE-OR-P-TRUE)
(GL::P-TRUE-IMPLIES-BDD-MODE-OR-P-TRUE)
(GL::BDD-MODE-IMPLIES-BDD-MODE-OR-P-TRUE)
(GL::AIG-MODE-OR-P-TRUE)
(GL::P-TRUE-IMPLIES-AIG-MODE-OR-P-TRUE)
(GL::AIG-MODE-IMPLIES-AIG-MODE-OR-P-TRUE)
(GL::BFR-UNPARAM-ENV)
(GL::BFR-EVAL-TO-PARAM-SPACE-WITH-UNPARAM-ENV
     (219 3
          (:DEFINITION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (155 5 (:DEFINITION AIG-RESTRICT))
     (142 142
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (126 6 (:DEFINITION UNPARAM-ENV))
     (122 122
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (117 3 (:DEFINITION TO-PARAM-SPACE))
     (112 28 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (99 3 (:REWRITE MAKE-FAL-IS-APPEND))
     (85 85 (:REWRITE DEFAULT-CDR))
     (75 25 (:DEFINITION BOOLEANP))
     (71 71 (:REWRITE DEFAULT-CAR))
     (70 14 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (57 14
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (54 4 (:DEFINITION BINARY-APPEND))
     (50 50 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 42
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (42 3 (:DEFINITION QCONS$INLINE))
     (39 39
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ASSIGNS-ALIST))
     (36 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (33 6
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (28 28
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (18 6 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (18 3 (:REWRITE ALISTP-WHEN-ATOM))
     (18 3 (:DEFINITION HONS-EQUAL))
     (17 17
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (15 15 (:TYPE-PRESCRIPTION UNPARAM-ENV))
     (12 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (10 2 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (9 9 (:DEFINITION HONS))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (6 3
        (:DEFINITION FLUSH-HONS-GET-HASH-TABLE-LINK))
     (3 3 (:TYPE-PRESCRIPTION ALISTP))
     (3 3
        (:REWRITE ALISTP-AIG-EXTRACT-ASSIGNS-ALIST))
     (3 3 (:DEFINITION FAST-ALIST-FREE))
     (2 2
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (2 2
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1)))
(GL::BFR-UNPARAM-ENV-OF-PARAM-ENV
     (64 64
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (56 14 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (54 54
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (52 2 (:DEFINITION PARAM-ENV))
     (43 43 (:REWRITE DEFAULT-CDR))
     (42 2 (:DEFINITION UNPARAM-ENV))
     (35 7 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (33 11 (:DEFINITION BOOLEANP))
     (30 30 (:REWRITE DEFAULT-CAR))
     (24 7 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
     (21 21
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (21 6
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (20 4 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (18 6 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (14 14
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (7 7
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (6 6 (:TYPE-PRESCRIPTION UNPARAM-ENV))
     (6 6
        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (6 6
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (4 4
        (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1)))
(GL::BFR-LOOKUP-OF-UNPARAM-BDD-ENV-OF-PARAM-ENV
     (84 4 (:DEFINITION UNPARAM-ENV))
     (32 32
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (16 16 (:REWRITE DEFAULT-CDR))
     (16 16 (:REWRITE DEFAULT-CAR))
     (16 16
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (9 3
        (:REWRITE GL::P-TRUE-IMPLIES-AIG-MODE-OR-P-TRUE)))
(GL::BFR-SEMANTIC-DEPENDS-ON)
(GL::BFR-SEMANTIC-DEPENDS-ON-SUFF (4 4 (:DEFINITION MV-NTH)))
(GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)
(GL::BFR-DEPENDS-ON (5 5
                       (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX)))
(GL::AIG-EVAL-UNDER-ENV-WITH-NON-AIG-VAR-MEMBER
     (227 62 (:REWRITE SET::IN-TAIL))
     (94 94
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (87 81 (:REWRITE DEFAULT-CDR))
     (75 25 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (72 22 (:DEFINITION BOOLEANP))
     (51 17
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (47 47 (:TYPE-PRESCRIPTION BOOLEANP))
     (47 47 (:REWRITE DEFAULT-CAR))
     (39 13 (:REWRITE SET::UNION-EMPTY-Y))
     (39 13 (:REWRITE SET::UNION-EMPTY-X))
     (34 34
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (30 6 (:REWRITE SET::INSERT-IDENTITY))
     (6 6 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (2 2
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY)))
(GL::BFR-EVAL-OF-SET-NON-DEP
     (374 11 (:DEFINITION AIG-VARS))
     (170 17
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (168 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (119 17
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (110 33 (:REWRITE SET::IN-TAIL))
     (105 21 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (88 88 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (84 84
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (63 63
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (63 21 (:DEFINITION BOOLEANP))
     (55 11 (:REWRITE SET::INSERT-IDENTITY))
     (52 52 (:REWRITE DEFAULT-CDR))
     (51 17 (:REWRITE NATP-WHEN-GTE-0))
     (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 42
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (42 42 (:REWRITE DEFAULT-CAR))
     (34 34 (:TYPE-PRESCRIPTION NATP))
     (34 34
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (33 11 (:REWRITE SET::UNION-EMPTY-Y))
     (33 11 (:REWRITE SET::UNION-EMPTY-X))
     (33 11 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (33 11 (:REWRITE SET::NEVER-IN-EMPTY))
     (26 10
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (20 5
         (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (17 17 (:REWRITE NATP-WHEN-INTEGERP))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (16 16
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (11 11 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (4 4
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX)))
(GL::BFR-DEPENDS-ON-OF-BFR-VAR
     (359 359
          (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (309 309
          (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (273 35
          (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
     (181 19
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (179 35 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (154 19 (:DEFINITION BOOLEANP))
     (126 18
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (70 70
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (55 20 (:REWRITE SET::IN-TAIL))
     (54 18 (:REWRITE NATP-WHEN-GTE-0))
     (40 40 (:TYPE-PRESCRIPTION BOOLEANP))
     (36 36 (:TYPE-PRESCRIPTION NATP))
     (36 36
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (32 32 (:TYPE-PRESCRIPTION GL::BFR-VAR))
     (25 5 (:REWRITE SET::INSERT-IDENTITY))
     (18 18 (:REWRITE NATP-WHEN-INTEGERP))
     (18 18 (:REWRITE DEFAULT-<-2))
     (18 18 (:REWRITE DEFAULT-<-1))
     (9 3 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (5 5 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (4 4
        (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1 (:REWRITE SET::UNION-EMPTY-Y))
     (3 1 (:REWRITE SET::UNION-EMPTY-X))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
(GL::NO-NEW-DEPS-OF-BFR-NOT
     (136 4 (:DEFINITION AIG-VARS))
     (40 12 (:REWRITE SET::IN-TAIL))
     (40 4
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (32 32 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (32 8 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (28 4
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (20 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (20 4 (:REWRITE SET::INSERT-IDENTITY))
     (20 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (16 16
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (12 12
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (12 4 (:REWRITE SET::UNION-EMPTY-Y))
     (12 4 (:REWRITE SET::UNION-EMPTY-X))
     (12 4 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (12 4 (:REWRITE SET::NEVER-IN-EMPTY))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (12 4 (:DEFINITION BOOLEANP))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (8 8
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (8 8
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE NATP-WHEN-INTEGERP))
     (4 4 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::NO-NEW-DEPS-OF-BFR-AND
     (204 6 (:DEFINITION AIG-VARS))
     (60 6
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (52 16 (:REWRITE SET::IN-TAIL))
     (48 12 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (44 44 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (42 6
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (30 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (30 6 (:REWRITE SET::INSERT-IDENTITY))
     (30 6 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (24 24
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (18 18
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (18 6 (:REWRITE SET::UNION-EMPTY-Y))
     (18 6 (:REWRITE SET::UNION-EMPTY-X))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (18 6 (:DEFINITION BOOLEANP))
     (15 5 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (15 5 (:REWRITE SET::NEVER-IN-EMPTY))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 12
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (12 12
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (12 12 (:REWRITE DEFAULT-CDR))
     (12 12 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::NO-NEW-DEPS-OF-BFR-OR
     (382 11 (:DEFINITION AIG-VARS))
     (102 31 (:REWRITE SET::IN-TAIL))
     (90 9
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (88 22 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (84 84 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (63 26 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (63 9
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (55 11 (:REWRITE SET::INSERT-IDENTITY))
     (55 11 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (44 44
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (41 11 (:DEFINITION BOOLEANP))
     (33 33
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (33 11 (:REWRITE SET::UNION-EMPTY-Y))
     (33 11 (:REWRITE SET::UNION-EMPTY-X))
     (30 10 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (30 10 (:REWRITE SET::NEVER-IN-EMPTY))
     (27 9 (:REWRITE NATP-WHEN-GTE-0))
     (26 26 (:TYPE-PRESCRIPTION BOOLEANP))
     (22 22
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (22 22 (:REWRITE DEFAULT-CDR))
     (22 22 (:REWRITE DEFAULT-CAR))
     (18 18 (:TYPE-PRESCRIPTION NATP))
     (18 18
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (11 11 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (9 9 (:REWRITE NATP-WHEN-INTEGERP))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::NO-NEW-DEPS-OF-BFR-XOR
     (720 21 (:DEFINITION AIG-VARS))
     (170 53 (:REWRITE SET::IN-TAIL))
     (168 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (150 15
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (148 148
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (111 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (105 21 (:REWRITE SET::INSERT-IDENTITY))
     (105 21 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (105 15
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (84 84
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (69 21 (:DEFINITION BOOLEANP))
     (63 63
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (63 21 (:REWRITE SET::UNION-EMPTY-Y))
     (63 21 (:REWRITE SET::UNION-EMPTY-X))
     (48 16 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (48 16 (:REWRITE SET::NEVER-IN-EMPTY))
     (45 45 (:TYPE-PRESCRIPTION BOOLEANP))
     (45 15 (:REWRITE NATP-WHEN-GTE-0))
     (42 42
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (42 42 (:REWRITE DEFAULT-CDR))
     (42 42 (:REWRITE DEFAULT-CAR))
     (30 30 (:TYPE-PRESCRIPTION NATP))
     (30 30
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (21 21 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (15 15 (:REWRITE NATP-WHEN-INTEGERP))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::NO-NEW-DEPS-OF-BFR-IFF
     (720 21 (:DEFINITION AIG-VARS))
     (170 53 (:REWRITE SET::IN-TAIL))
     (168 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (150 15
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (148 148
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (111 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (105 21 (:REWRITE SET::INSERT-IDENTITY))
     (105 21 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (105 15
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (84 84
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (69 21 (:DEFINITION BOOLEANP))
     (63 63
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (63 21 (:REWRITE SET::UNION-EMPTY-Y))
     (63 21 (:REWRITE SET::UNION-EMPTY-X))
     (48 16 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (48 16 (:REWRITE SET::NEVER-IN-EMPTY))
     (45 45 (:TYPE-PRESCRIPTION BOOLEANP))
     (45 15 (:REWRITE NATP-WHEN-GTE-0))
     (42 42
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (42 42 (:REWRITE DEFAULT-CDR))
     (42 42 (:REWRITE DEFAULT-CAR))
     (30 30 (:TYPE-PRESCRIPTION NATP))
     (30 30
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (21 21 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (15 15 (:REWRITE NATP-WHEN-INTEGERP))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::NO-NEW-DEPS-OF-BFR-ITE
     (932 29 (:DEFINITION AIG-VARS))
     (247 77 (:REWRITE SET::IN-TAIL))
     (240 24
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (232 58 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (168 24
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (165 67 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (145 29 (:REWRITE SET::INSERT-IDENTITY))
     (145 29 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (116 116
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (103 31 (:DEFINITION BOOLEANP))
     (87 87
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (87 29 (:REWRITE SET::UNION-EMPTY-Y))
     (87 29 (:REWRITE SET::UNION-EMPTY-X))
     (72 24 (:REWRITE NATP-WHEN-GTE-0))
     (69 23 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (67 67 (:TYPE-PRESCRIPTION BOOLEANP))
     (58 58
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (58 58 (:REWRITE DEFAULT-CDR))
     (58 58 (:REWRITE DEFAULT-CAR))
     (48 48 (:TYPE-PRESCRIPTION NATP))
     (48 48
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (29 29 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (24 24 (:REWRITE NATP-WHEN-INTEGERP))
     (24 24 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::NO-DEPS-OF-BFR-CONSTANTS
     (20 2
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (14 2
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (10 4 (:REWRITE SET::IN-TAIL))
     (8 2
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (6 2
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (2 2 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(GL::PBFR-SEMANTIC-DEPENDS-ON)
(GL::PBFR-SEMANTIC-DEPENDS-ON-SUFF (4 4 (:DEFINITION MV-NTH)))
(GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)
(GL::PBFR-DEPENDS-ON (3 3
                        (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE)))
(GL::PBFR-EVAL-OF-SET-NON-DEP
     (6 2
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (4 4
        (:TYPE-PRESCRIPTION GL::BFR-SEMANTIC-DEPENDS-ON)))
(GL::NON-VAR-IMPLIES-NOT-MEMBER-EXTRACT-ASSIGNS
     (1457 24 (:DEFINITION MEMBER-EQUAL))
     (667 59 (:REWRITE SUBSETP-MEMBER . 1))
     (592 16 (:REWRITE SUBSETP-APPEND1))
     (564 564
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (495 177 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (422 182 (:REWRITE SUBSETP-TRANS2))
     (403 177 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (369 41
          (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (318 129
          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (292 102 (:REWRITE SET::IN-TAIL))
     (260 52 (:REWRITE SET::INSERT-IDENTITY))
     (250 250
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (204 60 (:DEFINITION BOOLEANP))
     (182 182 (:REWRITE SUBSETP-TRANS))
     (159 53 (:REWRITE SET::UNION-EMPTY-Y))
     (159 53 (:REWRITE SET::UNION-EMPTY-X))
     (144 144 (:TYPE-PRESCRIPTION SET::SFIX))
     (131 131 (:TYPE-PRESCRIPTION BOOLEANP))
     (124 124 (:REWRITE DEFAULT-CAR))
     (108 108 (:REWRITE DEFAULT-CDR))
     (64 64 (:REWRITE SUBSETP-MEMBER . 4))
     (64 64 (:REWRITE INTERSECTP-MEMBER . 3))
     (64 64 (:REWRITE INTERSECTP-MEMBER . 2))
     (63 21 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (59 59 (:REWRITE SUBSETP-MEMBER . 2))
     (52 52 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (26 2 (:DEFINITION BINARY-APPEND))
     (12 4 (:REWRITE SET::SFIX-WHEN-EMPTY))
     (12 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (12 4
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (10 10 (:TYPE-PRESCRIPTION SET::INSERT))
     (2 2 (:DEFINITION IFF)))
(GL::NON-VAR-IMPLIES-NOT-IN-AIG-EXTRACT-ASSIGNS-ALIST
     (57 1 (:DEFINITION AIG-EXTRACT-ASSIGNS))
     (34 1 (:DEFINITION AIG-VARS))
     (21 5 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (18 18
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (18 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (18 1 (:DEFINITION BINARY-APPEND))
     (16 16 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (15 3 (:REWRITE SET::INSERT-IDENTITY))
     (14 5 (:REWRITE SET::IN-TAIL))
     (12 12
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (12 2 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (12 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (12 2 (:REWRITE ALISTP-WHEN-ATOM))
     (10 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (9 3 (:REWRITE SET::UNION-EMPTY-Y))
     (9 3 (:REWRITE SET::UNION-EMPTY-X))
     (9 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (8 8 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (6 6 (:REWRITE DEFAULT-CAR))
     (6 2 (:DEFINITION BOOLEANP))
     (5 5 (:REWRITE DEFAULT-CDR))
     (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
     (3 3 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (3 1 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (3 1 (:REWRITE SET::NEVER-IN-EMPTY)))
(GL::NON-VAR-IMPLIES-NON-VAR-IN-RESTRICT-WITH-ASSIGNS-ALIST
     (462 11
          (:REWRITE GL::NON-VAR-IMPLIES-NOT-IN-AIG-EXTRACT-ASSIGNS-ALIST))
     (412 8
          (:REWRITE MEMBER-AIG-VARS-AIG-RESTRICT))
     (384 123 (:REWRITE SET::IN-TAIL))
     (245 5
          (:REWRITE ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL))
     (148 60 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (125 25 (:REWRITE SET::INSERT-IDENTITY))
     (96 96
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (96 32 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (92 28 (:DEFINITION BOOLEANP))
     (84 28 (:REWRITE SET::UNION-EMPTY-Y))
     (84 28 (:REWRITE SET::UNION-EMPTY-X))
     (71 71 (:REWRITE DEFAULT-CDR))
     (66 11
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (60 60 (:TYPE-PRESCRIPTION BOOLEANP))
     (57 57
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ASSIGNS-ALIST))
     (48 48 (:REWRITE DEFAULT-CAR))
     (38 38
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (30 5 (:REWRITE ALIST-KEYS-WHEN-ATOM))
     (25 25 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (18 3 (:REWRITE ALIST-VALS-WHEN-ATOM)))
(GL::NON-VAR-IMPLIES-NOT-IN-AIG-EXTRACT-ITERATED-ASSIGNS-ALIST
     (294 15 (:DEFINITION AIG-VARS))
     (147 39 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (115 43 (:REWRITE SET::IN-TAIL))
     (105 42 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (84 24 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (78 13
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (75 15 (:REWRITE SET::INSERT-IDENTITY))
     (72 9 (:REWRITE SET::IN-INSERT))
     (66 66
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (63 21 (:DEFINITION BOOLEANP))
     (62 62
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (54 54
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (54 3 (:DEFINITION BINARY-APPEND))
     (53 53 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 42 (:REWRITE DEFAULT-CDR))
     (36 6
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (33 33 (:REWRITE DEFAULT-CAR))
     (33 14 (:REWRITE SET::NEVER-IN-EMPTY))
     (30 30
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (30 30
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (27 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (18 6 (:REWRITE SET::UNION-EMPTY-Y))
     (18 6 (:REWRITE SET::UNION-EMPTY-X))
     (18 3 (:REWRITE ALISTP-WHEN-ATOM))
     (15 15 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (15 5 (:REWRITE ZP-WHEN-GT-0))
     (15 5 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (5 5 (:REWRITE ZP-WHEN-INTEGERP))
     (5 5 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1)))
(GL::NON-VAR-IMPLIES-NON-VAR-IN-RESTRICT-WITH-ITERATED-ASSIGNS-ALIST
 (462
    11
    (:REWRITE GL::NON-VAR-IMPLIES-NOT-IN-AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
 (412 8
      (:REWRITE MEMBER-AIG-VARS-AIG-RESTRICT))
 (384 123 (:REWRITE SET::IN-TAIL))
 (245 5
      (:REWRITE ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL))
 (148 60 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (125 25 (:REWRITE SET::INSERT-IDENTITY))
 (96 96
     (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
 (96 32 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (92 28 (:DEFINITION BOOLEANP))
 (84 28 (:REWRITE SET::UNION-EMPTY-Y))
 (84 28 (:REWRITE SET::UNION-EMPTY-X))
 (71 71 (:REWRITE DEFAULT-CDR))
 (66 11
     (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (60 60 (:TYPE-PRESCRIPTION BOOLEANP))
 (57 57
     (:TYPE-PRESCRIPTION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
 (48 48 (:REWRITE DEFAULT-CAR))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (30 5 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (25 25 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (18 3 (:REWRITE ALIST-VALS-WHEN-ATOM)))
(GL::PBFR-DEPENDS-ON-OF-BFR-VAR
     (662 662
          (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (481 5
          (:DEFINITION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (466 60
          (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
     (435 87 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (384 384
          (:TYPE-PRESCRIPTION GL::BFR-VARNAME-FIX))
     (292 52 (:DEFINITION BOOLEANP))
     (241 84 (:REWRITE SET::IN-TAIL))
     (213 24
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (181 5 (:REWRITE MAKE-FAL-IS-APPEND))
     (164 164
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (147 21
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (135 27 (:REWRITE SET::INSERT-IDENTITY))
     (106 106 (:TYPE-PRESCRIPTION BOOLEANP))
     (106 106
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (100 5
          (:REWRITE GL::NON-VAR-IMPLIES-NOT-IN-AIG-EXTRACT-ASSIGNS-ALIST))
     (78 5 (:DEFINITION BINARY-APPEND))
     (70 70
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (65 65
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ASSIGNS-ALIST))
     (63 21 (:REWRITE NATP-WHEN-GTE-0))
     (61 61 (:REWRITE DEFAULT-CDR))
     (57 19 (:REWRITE SET::UNION-EMPTY-Y))
     (57 19 (:REWRITE SET::UNION-EMPTY-X))
     (54 9 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (53 53 (:REWRITE DEFAULT-CAR))
     (48 16 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (45 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (42 42 (:TYPE-PRESCRIPTION NATP))
     (42 42
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (39 39
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (36 6
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (30 30
         (:TYPE-PRESCRIPTION AIG-EXTRACT-ITERATED-ASSIGNS-ALIST))
     (30 5 (:REWRITE ALISTP-WHEN-ATOM))
     (30 5 (:DEFINITION HONS-EQUAL))
     (27 27 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (21 21 (:REWRITE NATP-WHEN-INTEGERP))
     (21 21 (:REWRITE DEFAULT-<-2))
     (21 21 (:REWRITE DEFAULT-<-1))
     (10 5
         (:DEFINITION FLUSH-HONS-GET-HASH-TABLE-LINK))
     (6 2
        (:REWRITE GL::PBFR-EVAL-OF-SET-NON-DEP))
     (5 5 (:TYPE-PRESCRIPTION ALISTP))
     (5 5
        (:REWRITE ALISTP-AIG-EXTRACT-ASSIGNS-ALIST))
     (5 5 (:DEFINITION FAST-ALIST-FREE))
     (4 4
        (:REWRITE GL::BFR-EVAL-TO-PARAM-SPACE-WITH-UNPARAM-ENV))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR)))
(GL::PBFR-DEPENDS-ON-OF-CONSTANTS
     (10 2
         (:REWRITE GL::PBFR-EVAL-OF-SET-NON-DEP))
     (8 2
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (6 2
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (6 2
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (4 4
        (:TYPE-PRESCRIPTION GL::BFR-SEMANTIC-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-NOT
     (172 4 (:DEFINITION AIG-VARS))
     (61 61
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (46 8 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (40 12 (:REWRITE SET::IN-TAIL))
     (40 4
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (34 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (32 32 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (28 4
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (28 4 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (22 4 (:DEFINITION BOOLEANP))
     (20 4 (:REWRITE SET::INSERT-IDENTITY))
     (16 16
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (12 12
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (12 4 (:REWRITE SET::UNION-EMPTY-Y))
     (12 4 (:REWRITE SET::UNION-EMPTY-X))
     (12 4 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (12 4 (:REWRITE SET::NEVER-IN-EMPTY))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (8 8
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (8 8
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE NATP-WHEN-INTEGERP))
     (4 4 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-AND
     (258 6 (:DEFINITION AIG-VARS))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (69 12 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (60 6
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (52 16 (:REWRITE SET::IN-TAIL))
     (51 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (44 44 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (42 6
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (42 6 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (33 6 (:DEFINITION BOOLEANP))
     (30 6 (:REWRITE SET::INSERT-IDENTITY))
     (24 24
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (18 18
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (18 6 (:REWRITE SET::UNION-EMPTY-Y))
     (18 6 (:REWRITE SET::UNION-EMPTY-X))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (15 5 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (15 5 (:REWRITE SET::NEVER-IN-EMPTY))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 12
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (12 12
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (12 12 (:REWRITE DEFAULT-CDR))
     (12 12 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-OR
     (436 11 (:DEFINITION AIG-VARS))
     (109 22 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (102 31 (:REWRITE SET::IN-TAIL))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (90 9
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (84 84 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (84 26 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (67 11 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (63 9
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (56 11 (:DEFINITION BOOLEANP))
     (55 11 (:REWRITE SET::INSERT-IDENTITY))
     (44 44
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (33 33
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (33 11 (:REWRITE SET::UNION-EMPTY-Y))
     (33 11 (:REWRITE SET::UNION-EMPTY-X))
     (30 10 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (30 10 (:REWRITE SET::NEVER-IN-EMPTY))
     (27 9 (:REWRITE NATP-WHEN-GTE-0))
     (26 26 (:TYPE-PRESCRIPTION BOOLEANP))
     (22 22
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (22 22 (:REWRITE DEFAULT-CDR))
     (22 22 (:REWRITE DEFAULT-CAR))
     (18 18 (:TYPE-PRESCRIPTION NATP))
     (18 18
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (11 11 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (9 9 (:REWRITE NATP-WHEN-INTEGERP))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-XOR
     (774 21 (:DEFINITION AIG-VARS))
     (189 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (170 53 (:REWRITE SET::IN-TAIL))
     (150 15
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (148 148
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (132 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (117 21 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (105 21 (:REWRITE SET::INSERT-IDENTITY))
     (105 15
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (84 84
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (84 21 (:DEFINITION BOOLEANP))
     (63 63
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (63 21 (:REWRITE SET::UNION-EMPTY-Y))
     (63 21 (:REWRITE SET::UNION-EMPTY-X))
     (48 16 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (48 16 (:REWRITE SET::NEVER-IN-EMPTY))
     (45 45 (:TYPE-PRESCRIPTION BOOLEANP))
     (45 15 (:REWRITE NATP-WHEN-GTE-0))
     (42 42
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (42 42 (:REWRITE DEFAULT-CDR))
     (42 42 (:REWRITE DEFAULT-CAR))
     (30 30 (:TYPE-PRESCRIPTION NATP))
     (30 30
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (21 21 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (15 15 (:REWRITE NATP-WHEN-INTEGERP))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-IFF
     (774 21 (:DEFINITION AIG-VARS))
     (189 42 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (170 53 (:REWRITE SET::IN-TAIL))
     (150 15
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (148 148
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (132 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (117 21 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (105 21 (:REWRITE SET::INSERT-IDENTITY))
     (105 15
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (84 84
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (84 21 (:DEFINITION BOOLEANP))
     (63 63
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (63 21 (:REWRITE SET::UNION-EMPTY-Y))
     (63 21 (:REWRITE SET::UNION-EMPTY-X))
     (48 16 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (48 16 (:REWRITE SET::NEVER-IN-EMPTY))
     (45 45 (:TYPE-PRESCRIPTION BOOLEANP))
     (45 15 (:REWRITE NATP-WHEN-GTE-0))
     (42 42
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (42 42 (:REWRITE DEFAULT-CDR))
     (42 42 (:REWRITE DEFAULT-CAR))
     (30 30 (:TYPE-PRESCRIPTION NATP))
     (30 30
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (21 21 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (15 15 (:REWRITE NATP-WHEN-INTEGERP))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-NOR
     (326 8 (:DEFINITION AIG-VARS))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (85 16 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (72 22 (:REWRITE SET::IN-TAIL))
     (61 16 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (60 60 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (60 6
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (52 8 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (42 6
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (40 8 (:REWRITE SET::INSERT-IDENTITY))
     (39 8 (:DEFINITION BOOLEANP))
     (32 32
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (24 24
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (24 8 (:REWRITE SET::UNION-EMPTY-Y))
     (24 8 (:REWRITE SET::UNION-EMPTY-X))
     (21 7 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (21 7 (:REWRITE SET::NEVER-IN-EMPTY))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (16 16 (:TYPE-PRESCRIPTION BOOLEANP))
     (16 16
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (16 16 (:REWRITE DEFAULT-CDR))
     (16 16 (:REWRITE DEFAULT-CAR))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (8 8 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-NAND
     (258 6 (:DEFINITION AIG-VARS))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (69 12 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (60 6
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (52 16 (:REWRITE SET::IN-TAIL))
     (51 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (44 44 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (42 6
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (42 6 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (33 6 (:DEFINITION BOOLEANP))
     (30 6 (:REWRITE SET::INSERT-IDENTITY))
     (24 24
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (18 18
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (18 6 (:REWRITE SET::UNION-EMPTY-Y))
     (18 6 (:REWRITE SET::UNION-EMPTY-X))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (15 5 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (15 5 (:REWRITE SET::NEVER-IN-EMPTY))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 12
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (12 12
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (12 12 (:REWRITE DEFAULT-CDR))
     (12 12 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-ANDC1
     (292 7 (:DEFINITION AIG-VARS))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (77 14 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (62 19 (:REWRITE SET::IN-TAIL))
     (60 6
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (56 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (52 52 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (47 7 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (42 6
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (36 7 (:DEFINITION BOOLEANP))
     (35 7 (:REWRITE SET::INSERT-IDENTITY))
     (28 28
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (21 21
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (21 7 (:REWRITE SET::UNION-EMPTY-Y))
     (21 7 (:REWRITE SET::UNION-EMPTY-X))
     (18 6 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (18 6 (:REWRITE SET::NEVER-IN-EMPTY))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
     (14 14
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (14 14 (:REWRITE DEFAULT-CDR))
     (14 14 (:REWRITE DEFAULT-CAR))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (7 7 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-ANDC2
     (292 7 (:DEFINITION AIG-VARS))
     (97 97
         (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (77 14 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (62 19 (:REWRITE SET::IN-TAIL))
     (60 6
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (56 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (52 52 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (47 7 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (42 6
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (36 7 (:DEFINITION BOOLEANP))
     (35 7 (:REWRITE SET::INSERT-IDENTITY))
     (28 28
         (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (21 21
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (21 7 (:REWRITE SET::UNION-EMPTY-Y))
     (21 7 (:REWRITE SET::UNION-EMPTY-X))
     (18 6 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (18 6 (:REWRITE SET::NEVER-IN-EMPTY))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
     (14 14
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (14 14 (:REWRITE DEFAULT-CDR))
     (14 14 (:REWRITE DEFAULT-CAR))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 12
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (7 7 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::NO-NEW-DEPS-OF-PBFR-ITE
     (1004 29 (:DEFINITION AIG-VARS))
     (260 58 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (247 77 (:REWRITE SET::IN-TAIL))
     (240 24
          (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (193 67 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (168 24
          (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (161 29 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (145 29 (:REWRITE SET::INSERT-IDENTITY))
     (137 137
          (:TYPE-PRESCRIPTION GL::BFR-FROM-PARAM-SPACE))
     (123 31 (:DEFINITION BOOLEANP))
     (116 116
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (87 87
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (87 29 (:REWRITE SET::UNION-EMPTY-Y))
     (87 29 (:REWRITE SET::UNION-EMPTY-X))
     (72 24 (:REWRITE NATP-WHEN-GTE-0))
     (69 23 (:REWRITE SET::TAIL-WHEN-EMPTY))
     (67 67 (:TYPE-PRESCRIPTION BOOLEANP))
     (58 58
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (58 58 (:REWRITE DEFAULT-CDR))
     (58 58 (:REWRITE DEFAULT-CAR))
     (48 48 (:TYPE-PRESCRIPTION NATP))
     (48 48
         (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (29 29 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (24 24 (:REWRITE NATP-WHEN-INTEGERP))
     (24 24 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-<-1))
     (4 1
        (:REWRITE GL::BFR-EVAL-OF-SET-NON-DEP))
     (3 1
        (:REWRITE GL::PBFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (3 1
        (:REWRITE GL::BFR-SEMANTIC-DEPENDS-ON-OF-SET-VAR))
     (1 1
        (:TYPE-PRESCRIPTION GL::BFR-DEPENDS-ON)))
(GL::PBFR-DEPENDS-ON-WHEN-BOOLEANP
     (4 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE)))
(GL::NTH-WHEN-BFR-ENV-EQUIV-IN-BDD-MODE
     (324 264
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (102 31 (:REWRITE ZP-WHEN-GT-0))
     (75 45 (:REWRITE DEFAULT-CAR))
     (67 31 (:REWRITE ZP-WHEN-INTEGERP))
     (64 4 (:REWRITE IFF*-WHEN-OTHER))
     (60 60
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (48 6 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
     (28 28 (:REWRITE ZP-OPEN))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-<-1))
     (22 19 (:REWRITE DEFAULT-+-2))
     (21 3 (:REWRITE NFIX-WHEN-NATP))
     (19 19 (:REWRITE DEFAULT-CDR))
     (19 19 (:REWRITE DEFAULT-+-1))
     (15 15 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (15 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 6 (:REWRITE NATP-WHEN-GTE-0))
     (6 6 (:TYPE-PRESCRIPTION ZP))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 4 (:REWRITE IFF*-OF-NONNILS)))
(GL::PARAM-ENV-UNDER-BFR-ENV-EQUIV-IND)
(GL::NTH-OF-NIL)
(GL::PARAM-ENV-UNDER-BFR-ENV-EQUIV
     (272 272
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (213 205 (:REWRITE DEFAULT-CAR))
     (144 18 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (72 18
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (36 36
         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (36 36 (:TYPE-PRESCRIPTION ALISTP))
     (36 36 (:REWRITE IFF*-WHEN-OTHER))
     (36 18
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (24 18 (:REWRITE DEFAULT-+-2))
     (20 20 (:REWRITE IFF*-OF-NONNILS))
     (18 18
         (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (18 18 (:REWRITE DEFAULT-+-1))
     (18 18 (:REWRITE ALISTP-WHEN-ATOM))
     (14 6 (:REWRITE ZP-WHEN-GT-0))
     (6 6 (:REWRITE ZP-WHEN-INTEGERP))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(GL::BFR-ENV-EQUIV-IMPLIES-BFR-ENV-EQUIV-BFR-PARAM-ENV-2
     (1080 28 (:DEFINITION PARAM-ENV))
     (690 602
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (213 213 (:REWRITE DEFAULT-CDR))
     (212 168 (:REWRITE DEFAULT-CAR))
     (180 180
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (174 3
          (:REWRITE GL::NTH-WHEN-BFR-ENV-EQUIV-IN-BDD-MODE))
     (92 21 (:REWRITE ZP-WHEN-GT-0))
     (66 21 (:REWRITE ZP-WHEN-INTEGERP))
     (60 4 (:REWRITE IFF*-WHEN-OTHER))
     (55 55 (:TYPE-PRESCRIPTION NFIX))
     (52 2 (:DEFINITION IFF))
     (46 40 (:REWRITE DEFAULT-<-2))
     (40 40 (:REWRITE DEFAULT-<-1))
     (36 4 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
     (22 4
         (:REWRITE GL::BFR-VARNAME-FIX-WHEN-BFR-VARNAME-P))
     (20 4 (:REWRITE NFIX-WHEN-NATP))
     (19 17 (:REWRITE DEFAULT-+-2))
     (17 17 (:REWRITE DEFAULT-+-1))
     (16 16 (:TYPE-PRESCRIPTION NATP))
     (16 8 (:REWRITE NATP-WHEN-GTE-0))
     (16 4 (:REWRITE NFIX-WHEN-NOT-NATP))
     (16 2
         (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
     (14 2
         (:REWRITE GL::BFR-VARNAME-P-WHEN-NATP))
     (10 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (8 8 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (8 8 (:REWRITE NATP-WHEN-INTEGERP))
     (7 7 (:TYPE-PRESCRIPTION AIG-ENV-LOOKUP))
     (6 6 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (5 3 (:DEFINITION AIG-ENV-LOOKUP))
     (4 4
        (:TYPE-PRESCRIPTION GL::BFR-VARNAME-P))
     (4 4
        (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (4 4 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 2 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (3 3 (:REWRITE IFF*-OF-NONNILS))
     (2 2 (:TYPE-PRESCRIPTION IFF))
     (1 1 (:TYPE-PRESCRIPTION HONS-GET)))
(GL::NTH-WHEN-BFR-ENV-EQUIV-IN-BDD-MODE
     (324 264
          (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (102 31 (:REWRITE ZP-WHEN-GT-0))
     (75 45 (:REWRITE DEFAULT-CAR))
     (67 31 (:REWRITE ZP-WHEN-INTEGERP))
     (64 4 (:REWRITE IFF*-WHEN-OTHER))
     (60 60
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (48 6 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
     (28 28 (:REWRITE ZP-OPEN))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-<-1))
     (22 19 (:REWRITE DEFAULT-+-2))
     (21 3 (:REWRITE NFIX-WHEN-NATP))
     (19 19 (:REWRITE DEFAULT-CDR))
     (19 19 (:REWRITE DEFAULT-+-1))
     (15 15 (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (15 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (12 12 (:TYPE-PRESCRIPTION NATP))
     (12 6 (:REWRITE NATP-WHEN-GTE-0))
     (6 6 (:TYPE-PRESCRIPTION ZP))
     (6 6 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 4 (:REWRITE IFF*-OF-NONNILS)))
(GL::UNPARAM-ENV-UNDER-BFR-ENV-EQUIV-IND)
(GL::NTH-OF-NIL)
(GL::UNPARAM-ENV-UNDER-BFR-ENV-EQUIV
     (272 237 (:REWRITE DEFAULT-CAR))
     (236 236
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (136 17 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (68 17
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (42 33 (:REWRITE DEFAULT-+-2))
     (34 34
         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (34 34 (:TYPE-PRESCRIPTION ALISTP))
     (34 17
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (33 33 (:REWRITE DEFAULT-+-1))
     (32 32 (:REWRITE IFF*-WHEN-OTHER))
     (29 13 (:REWRITE ZP-WHEN-GT-0))
     (24 24 (:REWRITE IFF*-OF-NONNILS))
     (17 17
         (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (17 17 (:REWRITE ALISTP-WHEN-ATOM))
     (13 13 (:REWRITE ZP-WHEN-INTEGERP))
     (13 13 (:REWRITE ZP-OPEN))
     (9 9
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1)))
(GL::BFR-ENV-EQUIV-IMPLIES-BFR-ENV-EQUIV-BFR-UNPARAM-ENV-2
     (3186 106 (:DEFINITION UNPARAM-ENV))
     (2188 1836
           (:REWRITE GL::BFR-ENV-EQUIV-OF-CDR-IN-BDD-MODE-IMPLIES-CAR))
     (826 650 (:REWRITE DEFAULT-CAR))
     (750 750
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (519 519 (:REWRITE DEFAULT-CDR))
     (494 26 (:REWRITE IFF*-WHEN-OTHER))
     (455 455 (:TYPE-PRESCRIPTION UNPARAM-ENV))
     (436 108 (:REWRITE ZP-WHEN-GT-0))
     (389 389
          (:TYPE-PRESCRIPTION GL::AIG-VAR-FIX))
     (300 108 (:REWRITE ZP-WHEN-INTEGERP))
     (288 32 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
     (200 25
          (:REWRITE GL::AIG-VAR-FIX-WHEN-AIG-VAR-P))
     (184 184 (:REWRITE DEFAULT-<-2))
     (184 184 (:REWRITE DEFAULT-<-1))
     (125 25 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (112 16 (:REWRITE NFIX-WHEN-NATP))
     (92 76 (:REWRITE DEFAULT-+-2))
     (80 16 (:REWRITE NFIX-WHEN-NOT-NATP))
     (76 76 (:REWRITE DEFAULT-+-1))
     (75 75
         (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (75 25
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (64 64 (:TYPE-PRESCRIPTION NATP))
     (64 32 (:REWRITE NATP-WHEN-GTE-0))
     (50 50
         (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (50 25 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (40 14
         (:REWRITE GL::NTH-WHEN-BFR-ENV-EQUIV-IN-BDD-MODE))
     (32 32 (:REWRITE NATP-WHEN-INTEGERP))
     (32 32
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (14 14 (:REWRITE IFF*-OF-NONNILS)))
