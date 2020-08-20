(RP::STINGY-PP-CLEAN)
(RP::CLEAN-PP-ARGS-COND)
(RP::GET-C-ARGS$INLINE)
(RP::INTEGERP-OF-GET-C-ARGS.HASH-CODE
     (62 62 (:REWRITE DEFAULT-CDR))
     (25 25 (:REWRITE DEFAULT-CAR))
     (16 1 (:DEFINITION RP::EX-FROM-RP))
     (14 2 (:REWRITE RP::IFIX-OPENER))
     (11 1 (:REWRITE RP::NOT-INCLUDE-RP))
     (10 2
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (8 1 (:DEFINITION RP::INCLUDE-FNC))
     (6 2 (:DEFINITION APPLY$-BADGEP))
     (4 4 (:TYPE-PRESCRIPTION O-P))
     (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2
        (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1))
     (2 1 (:DEFINITION QUOTEP))
     (1 1 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-OF-GET-C-ARGS.S-ARGS
     (1178 6 (:DEFINITION RP::RP-TERMP))
     (796 4 (:DEFINITION RP::FALIST-CONSISTENT))
     (616 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (614 614 (:REWRITE DEFAULT-CDR))
     (448 28 (:DEFINITION RP::EX-FROM-RP))
     (428 428 (:REWRITE DEFAULT-CAR))
     (332 32 (:REWRITE RP::NOT-INCLUDE-RP))
     (240 32 (:DEFINITION RP::INCLUDE-FNC))
     (188 53 (:REWRITE O-P-O-INFP-CAR))
     (88 88 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (88 20 (:REWRITE RP::IS-IF-RP-TERMP))
     (56 56
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (48 10 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (45 45 (:REWRITE O-P-DEF-O-FINP-1))
     (38 38
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (37 4 (:DEFINITION APPLY$-BADGEP))
     (36 8
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (32 8 (:REWRITE RP::RP-TERMP-CADR))
     (30 30
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (28 4
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (28 2
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (23 23 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (16 4
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (16 1 (:DEFINITION NATP))
     (14 2 (:REWRITE RP::IFIX-OPENER))
     (12 12 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (12 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (12 3
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (9 2
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 2
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (4 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERMP-OF-GET-C-ARGS.PP-ARGS
     (2239 14 (:DEFINITION RP::RP-TERMP))
     (1143 40 (:REWRITE RP::IS-IF-RP-TERMP))
     (917 6 (:DEFINITION RP::FALIST-CONSISTENT))
     (845 845 (:REWRITE DEFAULT-CDR))
     (832 52 (:DEFINITION RP::EX-FROM-RP))
     (647 6
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (633 633 (:REWRITE DEFAULT-CAR))
     (596 56 (:REWRITE RP::NOT-INCLUDE-RP))
     (432 56 (:DEFINITION RP::INCLUDE-FNC))
     (327 4 (:DEFINITION RP::RP-TERM-LISTP))
     (240 69 (:REWRITE O-P-O-INFP-CAR))
     (194 14
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (160 160
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (155 18 (:DEFINITION APPLY$-BADGEP))
     (120 9
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (104 104
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (64 5 (:DEFINITION NATP))
     (63 9
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (57 57 (:REWRITE O-P-DEF-O-FINP-1))
     (56 16 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (56 12
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (48 48
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (48 18 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (46 46 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (40 12 (:REWRITE RP::RP-TERMP-CADR))
     (40 12 (:REWRITE RP::RP-TERMP-CADDR))
     (38 38
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (36 14
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (33 33 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (28 11
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (24 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (16 4
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (14 2 (:REWRITE RP::IFIX-OPENER))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (11 11
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERM-LISTP-OF-GET-C-ARGS.C-ARG-LST
     (22675 2000 (:REWRITE RP::IS-IF-RP-TERMP))
     (17475 17457 (:REWRITE DEFAULT-CDR))
     (14515 117
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (14323 839 (:REWRITE RP::RP-TERMP-CADR))
     (12978 12966 (:REWRITE DEFAULT-CAR))
     (11315 557 (:DEFINITION APPLY$-BADGEP))
     (11310 338
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (9743 729 (:REWRITE RP::RP-TERMP-CADDR))
     (6610 60 (:DEFINITION SUBSETP-EQUAL))
     (5410 450 (:DEFINITION MEMBER-EQUAL))
     (5374 1505 (:REWRITE O-P-O-INFP-CAR))
     (3655 150 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (3400 240
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2519 2519
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (2264 736
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2219 361
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1572 360 (:REWRITE RP::RP-TERMP-CADDDR))
     (1331 1269 (:REWRITE O-P-DEF-O-FINP-1))
     (1286 557 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1118 98 (:DEFINITION NATP))
     (1105 230
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1018 1018
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (996 996 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (900 900 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (825 825 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (780 780 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (720 720
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (480 480
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (420 420 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (387 151
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (372 183
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (361 361
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (324 90
          (:REWRITE RP::EXTRACT-FROM-RP-PSEUDO-TERM-LISTP))
     (300 30
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (270 15 (:DEFINITION TRUE-LISTP))
     (234 36
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (183 183
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (150 150
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (120 60
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (117 18
          (:REWRITE RP::RP-TERMP-EXTRACT-FROM-RP))
     (117 18 (:REWRITE RP::RP-TERMP-EX-FROM-RP))
     (105 105 (:TYPE-PRESCRIPTION LEN))
     (105 15 (:DEFINITION LEN))
     (90 15 (:DEFINITION ALL-NILS))
     (85 5
         (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (75 75 (:TYPE-PRESCRIPTION ALL-NILS))
     (72 72
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (62 62 (:TYPE-PRESCRIPTION O-FINP))
     (60 60 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (30 30
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (30 30 (:LINEAR LEN-WHEN-PREFIXP))
     (30 15 (:REWRITE DEFAULT-+-2))
     (15 15 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (15 15 (:REWRITE DEFAULT-+-1))
     (15 15 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (15 15 (:LINEAR BOUNDS-POSITION-EQUAL))
     (14 2 (:REWRITE RP::IFIX-OPENER)))
(RP::SYMBOLP-OF-GET-C-ARGS.VALID)
(RP::PP-INSTANCE-HASH$INLINE)
(RP::INTEGERP-OF-PP-INSTANCE-HASH)
(RP::APPLY$-WARRANT-PP-INSTANCE-HASH$INLINE)
(RP::APPLY$-WARRANT-PP-INSTANCE-HASH$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-PP-INSTANCE-HASH$INLINE-NECC)
(RP::APPLY$-PP-INSTANCE-HASH$INLINE (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
                                    (2 2 (:REWRITE DEFAULT-CAR))
                                    (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
                                    (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::PP-LST-HASH)
(RP::INTEGERP-OF-PP-LST-HASH)
(RP::APPLY$-WARRANT-PP-LST-HASH)
(RP::APPLY$-WARRANT-PP-LST-HASH-DEFINITION)
(RP::APPLY$-WARRANT-PP-LST-HASH-NECC)
(RP::APPLY$-PP-LST-HASH (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
                        (2 2 (:REWRITE DEFAULT-CAR))
                        (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
                        (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::CALCULATE-PP-HASH$INLINE)
(RP::INTEGERP-OF-CALCULATE-PP-HASH)
(RP::APPLY$-WARRANT-CALCULATE-PP-HASH$INLINE)
(RP::APPLY$-WARRANT-CALCULATE-PP-HASH$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-CALCULATE-PP-HASH$INLINE-NECC)
(RP::APPLY$-CALCULATE-PP-HASH$INLINE (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
                                     (2 2 (:REWRITE DEFAULT-CAR))
                                     (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
                                     (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::GET-HASH-CODE-OF-SINGLE-S$INLINE)
(RP::INTEGERP-OF-GET-HASH-CODE-OF-SINGLE-S)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-SINGLE-S$INLINE)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-SINGLE-S$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-SINGLE-S$INLINE-NECC)
(RP::APPLY$-GET-HASH-CODE-OF-SINGLE-S$INLINE
     (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
     (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::GET-HASH-CODE-OF-S-LST$INLINE)
(RP::INTEGERP-OF-GET-HASH-CODE-OF-S-LST)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-S-LST$INLINE)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-S-LST$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-S-LST$INLINE-NECC)
(RP::APPLY$-GET-HASH-CODE-OF-S-LST$INLINE
     (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
     (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::GET-HASH-CODE-OF-S$INLINE)
(RP::INTEGERP-OF-GET-HASH-CODE-OF-S)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-S$INLINE)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-S$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-S$INLINE-NECC)
(RP::APPLY$-GET-HASH-CODE-OF-S$INLINE (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
                                      (2 2 (:REWRITE DEFAULT-CAR))
                                      (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
                                      (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::GET-HASH-CODE-OF-SINGLE-C$INLINE)
(RP::INTEGERP-OF-GET-HASH-CODE-OF-SINGLE-C)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-SINGLE-C$INLINE)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-SINGLE-C$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-GET-HASH-CODE-OF-SINGLE-C$INLINE-NECC)
(RP::APPLY$-GET-HASH-CODE-OF-SINGLE-C$INLINE
     (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
     (2 1 (:REWRITE APPLY$-PRIMITIVE)))
(RP::GET-HASH-CODE-OF-C-LST$INLINE)
(RP::INTEGERP-OF-GET-HASH-CODE-OF-C-LST)
(RP::GET-HASH-CODE-OF-C$INLINE)
(RP::INTEGERP-OF-GET-HASH-CODE-OF-C)
(RP::CALCULATE-S-HASH)
(RP::INTEGERP-OF-CALCULATE-S-HASH)
(RP::CALCULATE-C-HASH)
(RP::INTEGERP-OF-CALCULATE-C-HASH)
(RP::MEASURE-LEMMA-LOOSE1 (29 29 (:TYPE-PRESCRIPTION RP::CONS-COUNT))
                          (20 2 (:REWRITE RP::NOT-INCLUDE-RP))
                          (19 1 (:REWRITE O<=-O-FINP-DEF))
                          (17 1 (:REWRITE O-FINP-<))
                          (14 2 (:DEFINITION RP::INCLUDE-FNC))
                          (11 11 (:REWRITE DEFAULT-CAR))
                          (6 6 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                          (6 1 (:REWRITE O-FIRST-EXPT-<))
                          (4 4
                             (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                          (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (4 2 (:REWRITE DEFAULT-<-2))
                          (4 2 (:REWRITE DEFAULT-<-1))
                          (4 2 (:DEFINITION QUOTEP))
                          (3 1 (:REWRITE AC-<))
                          (2 2 (:REWRITE RP::MEASURE-LEMMA7-2))
                          (2 2
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                          (2 2
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                          (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                          (2 1 (:REWRITE O-FIRST-COEFF-<))
                          (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                          (1 1
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA2)))
(RP::MEASURE-LEMMA-LOOSE2 (352 12 (:REWRITE O<=-O-FINP-DEF))
                          (230 15
                               (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
                          (196 39 (:REWRITE O-P-O-INFP-CAR))
                          (190 190
                               (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                          (170 82 (:DEFINITION QUOTEP))
                          (108 32
                               (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                          (102 20 (:REWRITE RP::MEASURE-LEMMA6))
                          (97 29 (:REWRITE DEFAULT-+-2))
                          (84 32
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                          (79 39 (:REWRITE O-P-DEF-O-FINP-1))
                          (69 32 (:REWRITE DEFAULT-<-2))
                          (66 13 (:REWRITE O-FIRST-EXPT-<))
                          (64 32 (:REWRITE DEFAULT-<-1))
                          (58 16 (:REWRITE AC-<))
                          (48 29 (:REWRITE DEFAULT-+-1))
                          (40 40 (:TYPE-PRESCRIPTION O-FINP))
                          (40 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (32 32 (:REWRITE FOLD-CONSTS-IN-+))
                          (26 13 (:REWRITE O-FIRST-COEFF-<))
                          (23 23 (:REWRITE CAR-CONS))
                          (23 12 (:REWRITE O-INFP-O-FINP-O<=))
                          (21 7 (:REWRITE RP::M-MEASURE-LEMMA6))
                          (20 20
                              (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
                          (17 17 (:REWRITE CDR-CONS))
                          (15 15
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                          (9 3 (:REWRITE RP::IS-IF-CONS-COUNT))
                          (7 7 (:REWRITE RP::MEASURE-LEMMA7-2))
                          (7 7 (:REWRITE RP::MEASURE-LEMMA7))
                          (7 7 (:REWRITE RP::MEASURE-LEMMA6-5))
                          (7 7 (:REWRITE RP::M-MEASURE-LEMMA11))
                          (2 1
                             (:REWRITE RP::SUM-WITH-POSITIVE-LEMMA3)))
(RP::MEASURE-LEMMA-LOOSE3 (189 189
                               (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                          (179 15
                               (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
                          (155 29 (:REWRITE O-P-O-INFP-CAR))
                          (96 28 (:REWRITE DEFAULT-+-2))
                          (86 80 (:DEFINITION QUOTEP))
                          (68 29 (:REWRITE O-P-DEF-O-FINP-1))
                          (66 13 (:REWRITE O-FIRST-EXPT-<))
                          (58 16 (:REWRITE AC-<))
                          (55 17
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                          (51 10 (:REWRITE RP::MEASURE-LEMMA6))
                          (46 28 (:REWRITE DEFAULT-+-1))
                          (43 17
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                          (40 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (39 39 (:TYPE-PRESCRIPTION O-FINP))
                          (34 17 (:REWRITE DEFAULT-<-2))
                          (34 17 (:REWRITE DEFAULT-<-1))
                          (32 32 (:REWRITE FOLD-CONSTS-IN-+))
                          (26 13 (:REWRITE O-FIRST-COEFF-<))
                          (23 12 (:REWRITE O-INFP-O-FINP-O<=))
                          (22 22 (:REWRITE CAR-CONS))
                          (16 16
                              (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
                          (16 16 (:REWRITE CDR-CONS))
                          (15 5 (:REWRITE RP::M-MEASURE-LEMMA6))
                          (9 3 (:REWRITE RP::IS-IF-CONS-COUNT))
                          (5 5 (:REWRITE RP::MEASURE-LEMMA7-2))
                          (5 5 (:REWRITE RP::MEASURE-LEMMA7))
                          (5 5 (:REWRITE RP::MEASURE-LEMMA6-5))
                          (5 5 (:REWRITE RP::M-MEASURE-LEMMA11))
                          (2 2
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA2)))
(RP::MEASURE-LEMMA-LOOSE4 (187 187
                               (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                          (163 14
                               (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
                          (155 29 (:REWRITE O-P-O-INFP-CAR))
                          (85 79 (:DEFINITION QUOTEP))
                          (82 24 (:REWRITE DEFAULT-+-2))
                          (68 29 (:REWRITE O-P-DEF-O-FINP-1))
                          (66 13 (:REWRITE O-FIRST-EXPT-<))
                          (57 16 (:REWRITE AC-<))
                          (55 17
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                          (51 10 (:REWRITE RP::MEASURE-LEMMA6))
                          (43 17
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                          (40 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (39 39 (:TYPE-PRESCRIPTION O-FINP))
                          (39 24 (:REWRITE DEFAULT-+-1))
                          (34 17 (:REWRITE DEFAULT-<-2))
                          (34 17 (:REWRITE DEFAULT-<-1))
                          (26 26 (:REWRITE FOLD-CONSTS-IN-+))
                          (26 13 (:REWRITE O-FIRST-COEFF-<))
                          (23 12 (:REWRITE O-INFP-O-FINP-O<=))
                          (21 21 (:REWRITE CAR-CONS))
                          (16 16
                              (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
                          (15 15 (:REWRITE CDR-CONS))
                          (15 5 (:REWRITE RP::M-MEASURE-LEMMA6))
                          (9 3 (:REWRITE RP::IS-IF-CONS-COUNT))
                          (5 5 (:REWRITE RP::MEASURE-LEMMA7-2))
                          (5 5 (:REWRITE RP::MEASURE-LEMMA7))
                          (5 5 (:REWRITE RP::MEASURE-LEMMA6-5))
                          (5 5 (:REWRITE RP::M-MEASURE-LEMMA11))
                          (2 2
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA2)))
(RP::LOCAL-MEASURE-LEMMA4 (12 3 (:REWRITE O-FIRST-EXPT-<))
                          (9 9 (:REWRITE DEFAULT-<-2))
                          (9 9 (:REWRITE DEFAULT-<-1))
                          (9 3 (:REWRITE O<=-O-FINP-DEF))
                          (9 3 (:REWRITE O-FINP-<))
                          (6 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
                          (3 3 (:REWRITE O-INFP-O-FINP-O<=))
                          (3 3 (:REWRITE O-FIRST-COEFF-<))
                          (3 3
                             (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                          (3 3 (:REWRITE AC-<)))
(RP::LOCAL-MEASURE-LEMMA5 (96 34 (:REWRITE DEFAULT-+-2))
                          (69 3 (:REWRITE O<=-O-FINP-DEF))
                          (65 65 (:REWRITE DEFAULT-CDR))
                          (62 34 (:REWRITE DEFAULT-+-1))
                          (21 21 (:REWRITE FOLD-CONSTS-IN-+))
                          (21 21 (:REWRITE DEFAULT-CAR))
                          (15 5 (:REWRITE DEFAULT-<-2))
                          (14 3 (:REWRITE AC-<))
                          (12 2 (:REWRITE O-FIRST-EXPT-<))
                          (10 5 (:REWRITE DEFAULT-<-1))
                          (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (8 2 (:REWRITE O-P-O-INFP-CAR))
                          (6 3 (:REWRITE O-INFP-O-FINP-O<=))
                          (6 3 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                          (4 2 (:REWRITE O-FIRST-COEFF-<))
                          (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
                          (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::LOCAL-MEASURE-LEMMA6 (70 27 (:REWRITE DEFAULT-+-2))
                          (64 3 (:REWRITE O<=-O-FINP-DEF))
                          (49 49 (:REWRITE DEFAULT-CDR))
                          (49 27 (:REWRITE DEFAULT-+-1))
                          (19 19 (:REWRITE DEFAULT-CAR))
                          (14 5 (:REWRITE DEFAULT-<-2))
                          (13 13 (:REWRITE FOLD-CONSTS-IN-+))
                          (13 3 (:REWRITE AC-<))
                          (12 2 (:REWRITE O-FIRST-EXPT-<))
                          (10 5 (:REWRITE DEFAULT-<-1))
                          (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (8 2 (:REWRITE O-P-O-INFP-CAR))
                          (6 3 (:REWRITE O-INFP-O-FINP-O<=))
                          (6 3 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                          (4 2 (:REWRITE O-FIRST-COEFF-<))
                          (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
                          (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::LOCAL-MEASURE-LEMMA7
     (14213 217 (:DEFINITION RP::EX-FROM-RP))
     (13597 267 (:REWRITE RP::NOT-INCLUDE-RP))
     (13451 49 (:DEFINITION RP::INCLUDE-FNC))
     (12587 19 (:DEFINITION APPLY$-BADGEP))
     (9022 954 (:REWRITE RP::MEASURE-LEMMA1-2))
     (8512 1528 (:REWRITE RP::MEASURE-LEMMA1))
     (7517 60 (:DEFINITION SUBSETP-EQUAL))
     (7421 48
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (6589 450 (:DEFINITION MEMBER-EQUAL))
     (5306 61
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3954 102 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (3835 240
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3564 2588 (:REWRITE DEFAULT-CDR))
     (2431 28
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (2075 28 (:DEFINITION RP::RP-TERM-LISTP))
     (1750 835 (:REWRITE DEFAULT-CAR))
     (1466 21 (:DEFINITION TRUE-LISTP))
     (900 900 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (780 780 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (720 720
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (713 713
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (486 144 (:REWRITE RP::IS-IF-RP-TERMP))
     (480 480
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (431 34 (:DEFINITION NATP))
     (415 21 (:DEFINITION ALL-NILS))
     (407 85 (:DEFINITION QUOTEP))
     (394 21 (:DEFINITION LEN))
     (364 364
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (301 301 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (282 36
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (241 19 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (228 228 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (162 48 (:REWRITE RP::RP-TERMP-CADDDR))
     (144 144
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (144 48 (:REWRITE RP::RP-TERMP-CADR))
     (144 48 (:REWRITE RP::RP-TERMP-CADDR))
     (144 48 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (112 56
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (108 36
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (106 53
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (102 102
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (102 43
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (96 96
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (81 3 (:REWRITE O-FINP-<))
     (70 2 (:REWRITE RP::EX-FROM-RP-X2))
     (68 4 (:REWRITE RP::MEASURE-LEMMA6))
     (60 60
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (53 53
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (36 36 (:TYPE-PRESCRIPTION QUOTEP))
     (34 18 (:REWRITE RP::CONS-COUNT-ATOM))
     (33 24 (:REWRITE DEFAULT-<-2))
     (33 24 (:REWRITE DEFAULT-<-1))
     (28 28
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (26 4 (:REWRITE |a < b & b < c  =>  a < c|))
     (25 25
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
     (24 24
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (24 12
         (:REWRITE RP::RP-TERMP-EXTRACT-FROM-RP))
     (24 12 (:REWRITE RP::RP-TERMP-EX-FROM-RP))
     (24 12
         (:REWRITE RP::EXTRACT-FROM-RP-PSEUDO-TERM-LISTP))
     (22 22
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (21 21 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (21 21 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (17 17 (:TYPE-PRESCRIPTION ALL-NILS))
     (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (14 7 (:REWRITE DEFAULT-+-2))
     (14 3 (:REWRITE O-FIRST-EXPT-<))
     (13 13 (:TYPE-PRESCRIPTION LEN))
     (12 3 (:REWRITE O-P-O-INFP-CAR))
     (9 3 (:REWRITE AC-<))
     (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 3 (:REWRITE O-INFP-O-FINP-O<=))
     (4 2 (:REWRITE O-FIRST-COEFF-<))
     (3 3 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2 (:LINEAR LEN-WHEN-PREFIXP))
     (1 1 (:REWRITE |~(a < a)|))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::LOCAL-MEASURE-LEMMA8 (432 12 (:DEFINITION RP::EX-FROM-RP))
                          (276 12 (:REWRITE RP::NOT-INCLUDE-RP))
                          (240 12 (:DEFINITION RP::INCLUDE-FNC))
                          (204 204 (:REWRITE RP::MEASURE-LEMMA1))
                          (139 41 (:REWRITE DEFAULT-CAR))
                          (133 61 (:REWRITE DEFAULT-CDR))
                          (133 5 (:REWRITE O-FINP-<))
                          (102 6 (:REWRITE RP::MEASURE-LEMMA6))
                          (72 12 (:DEFINITION QUOTEP))
                          (68 6 (:REWRITE |a < b & b < c  =>  a < c|))
                          (52 52 (:REWRITE RP::MEASURE-LEMMA1-2))
                          (36 36 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                          (30 20 (:REWRITE RP::CONS-COUNT-ATOM))
                          (28 14 (:REWRITE DEFAULT-<-2))
                          (28 14 (:REWRITE DEFAULT-<-1))
                          (24 24
                              (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                          (22 5 (:REWRITE O-FIRST-EXPT-<))
                          (15 15
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                          (15 5 (:REWRITE AC-<))
                          (14 14
                              (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                          (14 14
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                          (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                          (12 1 (:REWRITE RP::IS-RP-CONS-COUNT))
                          (10 10
                              (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                          (8 4 (:REWRITE O-INFP-O-FINP-O<=))
                          (8 4 (:REWRITE O-FIRST-COEFF-<))
                          (5 1 (:DEFINITION ATOM))
                          (3 1 (:REWRITE RP::M-MEASURE-LEMMA7))
                          (2 1 (:DEFINITION EQ))
                          (1 1 (:TYPE-PRESCRIPTION ATOM))
                          (1 1 (:REWRITE |~(a < a)|))
                          (1 1 (:REWRITE RP::MEASURE-LEMMA-LOOSE3))
                          (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::LOCAL-MEASURE-LEMMA10 (102 3 (:DEFINITION RP::EX-FROM-RP))
                           (73 52 (:REWRITE RP::MEASURE-LEMMA1))
                           (57 3 (:REWRITE RP::NOT-INCLUDE-RP))
                           (48 3 (:DEFINITION RP::INCLUDE-FNC))
                           (33 1 (:REWRITE RP::EX-FROM-RP-X2))
                           (30 10 (:REWRITE DEFAULT-CDR))
                           (25 9 (:REWRITE DEFAULT-CAR))
                           (14 14 (:REWRITE RP::MEASURE-LEMMA1-2))
                           (10 3 (:DEFINITION QUOTEP))
                           (10 1 (:REWRITE O<=-O-FINP-DEF))
                           (9 9 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                           (8 2 (:REWRITE RP::CONS-COUNT-ATOM))
                           (6 6
                              (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                           (3 3 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                           (3 1 (:REWRITE AC-<))
                           (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                           (2 1 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                           (1 1
                              (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::LOCAL-MEASURE-LEMMA11
     (1944 15
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1938 3 (:DEFINITION APPLY$-BADGEP))
     (1290 12 (:DEFINITION SUBSETP-EQUAL))
     (1050 90 (:DEFINITION MEMBER-EQUAL))
     (717 30 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (660 48
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (513 79 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
     (345 6
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (264 6 (:DEFINITION RP::RP-TERM-LISTP))
     (253 48 (:REWRITE O<=-O-FINP-DEF))
     (201 3 (:DEFINITION TRUE-LISTP))
     (180 180 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (156 156 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (146 49 (:DEFINITION QUOTEP))
     (144 144
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (121 42 (:REWRITE O-FIRST-EXPT-<))
     (100 52 (:REWRITE AC-<))
     (99 12
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (97 56 (:REWRITE DEFAULT-<-2))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (84 84 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (84 84
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (82 6
         (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (66 56 (:REWRITE DEFAULT-<-1))
     (66 34 (:REWRITE DEFAULT-+-2))
     (66 13 (:REWRITE O-P-O-INFP-CAR))
     (60 34 (:REWRITE DEFAULT-+-1))
     (58 48 (:REWRITE O-INFP-O-FINP-O<=))
     (58 35 (:REWRITE O-FIRST-COEFF-<))
     (57 6 (:DEFINITION NATP))
     (54 18 (:REWRITE RP::IS-IF-RP-TERMP))
     (51 51 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (38 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (36 12
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (30 30
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (30 30
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (27 13 (:REWRITE O-P-DEF-O-FINP-1))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (24 12
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (21 21 (:TYPE-PRESCRIPTION LEN))
     (21 3 (:DEFINITION LEN))
     (18 18
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (18 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (18 6 (:REWRITE RP::RP-TERMP-CADR))
     (18 6 (:REWRITE RP::RP-TERMP-CADDR))
     (18 6 (:REWRITE RP::RP-TERMP-CADDDR))
     (18 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (18 3 (:DEFINITION ALL-NILS))
     (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
     (14 14 (:TYPE-PRESCRIPTION O-FINP))
     (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (12 12 (:TYPE-PRESCRIPTION QUOTEP))
     (12 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (9 9 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (7 7 (:REWRITE |~(a < a)|))
     (6 6
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::GET-MAX-MIN-VAL (84 84 (:REWRITE DEFAULT-CDR))
                     (12 12 (:REWRITE RP::CONS-COUNT-ATOM))
                     (12 6 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                     (6 6 (:TYPE-PRESCRIPTION RP::CONS-COUNT))
                     (5 1 (:REWRITE RP::LOCAL-MEASURE-LEMMA7))
                     (4 1 (:REWRITE RP::LOCAL-MEASURE-LEMMA8)))
(RP::GET-MAX-MIN-VAL-FLAG (84 84 (:REWRITE DEFAULT-CDR))
                          (12 12 (:REWRITE RP::CONS-COUNT-ATOM))
                          (12 6 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                          (6 6 (:TYPE-PRESCRIPTION RP::CONS-COUNT))
                          (5 1 (:REWRITE RP::LOCAL-MEASURE-LEMMA7))
                          (4 1 (:REWRITE RP::LOCAL-MEASURE-LEMMA8)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::GET-MAX-MIN-VAL-FLAG-EQUIVALENCES)
(RP::FLAG-LEMMA-FOR-RETURN-TYPE-OF-GET-MAX-MIN-VAL.MAX-VAL
     (1666 1666
           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (819 273
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (546 546 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (126 42 (:REWRITE RP::F2-OF-BIT))
     (102 102 (:REWRITE DEFAULT-+-2))
     (102 102 (:REWRITE DEFAULT-+-1))
     (42 42 (:TYPE-PRESCRIPTION BITP))
     (42 42 (:DEFINITION BITP))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::RETURN-TYPE-OF-GET-MAX-MIN-VAL.MAX-VAL)
(RP::RETURN-TYPE-OF-GET-MAX-MIN-VAL.MIN-VAL)
(RP::RETURN-TYPE-OF-GET-MAX-MIN-VAL.VALID)
(RP::RETURN-TYPE-OF-GET-MAX-MIN-VAL-LST.MAX-VAL)
(RP::RETURN-TYPE-OF-GET-MAX-MIN-VAL-LST.MIN-VAL)
(RP::RETURN-TYPE-OF-GET-MAX-MIN-VAL-LST.VALID)
(RP::GET-MAX-MIN-VAL-LST
     (2952 164
           (:DEFINITION RP::GET-MAX-MIN-VAL-LST))
     (1674 1674 (:REWRITE DEFAULT-CDR))
     (1578 806
           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1510 410 (:REWRITE DEFAULT-+-1))
     (1498 410 (:REWRITE DEFAULT-+-2))
     (824 824
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (806 806
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (285 1 (:DEFINITION RP::GET-MAX-MIN-VAL))
     (208 2 (:DEFINITION FLOOR))
     (168 56
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (112 112 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (98 4
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (48 2 (:REWRITE COMMUTATIVITY-OF-*))
     (42 20 (:REWRITE RATIONALP-+))
     (42 4 (:REWRITE DISTRIBUTIVITY))
     (34 4 (:DEFINITION NFIX))
     (24 12 (:REWRITE DEFAULT-*-2))
     (20 12
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (18 10 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 12
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
     (12 12
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE DEFAULT-*-1))
     (12 2 (:REWRITE DEFAULT-NUMERATOR))
     (10 10
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (10 10 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 2 (:REWRITE DEFAULT-DENOMINATOR))
     (4 4 (:REWRITE RP::IFIX-OPENER))
     (4 2 (:REWRITE RATIONALP-*))
     (4 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (4 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (4 2 (:REWRITE RP::FLOOR2-IF-F2)))
(RP::IS-C-BITP-TRAVERSE)
(RP::BOOLEANP-OF-IS-C-BITP-TRAVERSE)
(RP::PP-LST-SUBSETP (132 2 (:REWRITE O<=-O-FINP-DEF))
                    (124 4
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA8))
                    (68 4 (:REWRITE RP::MEASURE-LEMMA6))
                    (34 34 (:REWRITE RP::MEASURE-LEMMA1))
                    (34 18 (:REWRITE RP::CONS-COUNT-ATOM))
                    (20 10 (:REWRITE DEFAULT-<-2))
                    (20 10 (:REWRITE DEFAULT-<-1))
                    (10 10
                        (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                    (10 10
                        (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                    (10 5 (:REWRITE DEFAULT-+-2))
                    (10 5 (:REWRITE DEFAULT-+-1))
                    (10 2 (:REWRITE AC-<))
                    (6 6 (:REWRITE RP::MEASURE-LEMMA1-2))
                    (6 6
                       (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                    (6 6 (:REWRITE DEFAULT-CAR))
                    (6 2 (:REWRITE O-INFP-O-FINP-O<=))
                    (6 2 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                    (3 3 (:REWRITE DEFAULT-CDR))
                    (2 2
                       (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::PP-SUBSETP)
(RP::RP-TERM-LISTP-OF-CONS
     (10 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (6 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6 2 (:DEFINITION QUOTEP))
     (5 5 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE DEFAULT-CDR))
     (2 2 (:TYPE-PRESCRIPTION QUOTEP))
     (2 2
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-OF-- (5 5 (:REWRITE DEFAULT-CAR))
                   (1 1 (:REWRITE DEFAULT-CDR)))
(RP::RP-TERMP-OF-LIST (5 5 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE DEFAULT-CDR)))
(RP::RP-TERMP-OF-S-AND-C (10 10 (:REWRITE DEFAULT-CAR))
                         (2 2 (:REWRITE DEFAULT-CDR)))
(RP::RP-TERMP-CAR-CDDDDR
     (20127 897 (:REWRITE RP::IS-IF-RP-TERMP))
     (19017 153 (:DEFINITION RP::RP-TERM-LISTP))
     (13020 81
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (11463 11463 (:REWRITE DEFAULT-CDR))
     (11283 336 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (11190 216 (:REWRITE RP::RP-TERMP-CADDDR))
     (11079 285 (:REWRITE RP::RP-TERMP-CADDR))
     (8094 8094 (:REWRITE DEFAULT-CAR))
     (4686 1293 (:REWRITE O-P-O-INFP-CAR))
     (2895 517
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2262 2262 (:TYPE-PRESCRIPTION O-P))
     (1590 288 (:REWRITE RP::RP-TERMP-CADR))
     (1463 307
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1173 517
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1131 1131 (:REWRITE O-P-DEF-O-FINP-1))
     (1026 1026
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (717 717 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (705 705
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (307 307
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (198 66
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (132 132 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (114 114
          (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (78 78 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (12 4 (:REWRITE RP::NOT-INCLUDE-RP))
     (8 8 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC)))
(RP::RP-TERMP-OF-CONSED (308 2
                             (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                        (202 202 (:REWRITE DEFAULT-CDR))
                        (138 138 (:REWRITE DEFAULT-CAR))
                        (76 22 (:REWRITE O-P-O-INFP-CAR))
                        (36 36 (:TYPE-PRESCRIPTION O-P))
                        (18 18 (:REWRITE O-P-DEF-O-FINP-1))
                        (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                        (6 2 (:REWRITE RP::NOT-INCLUDE-RP))
                        (4 4 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                        (2 2
                           (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                        (2 2
                           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::ABS-TERM$INLINE)
(RP::RP-TERMP-OF-ABS-TERM.ABS
     (8 8 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (3 1 (:REWRITE RP::IS-IF-RP-TERMP))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (2 2
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)))
(RP::BOOLEANP-OF-ABS-TERM.SIGNED (4 4 (:REWRITE DEFAULT-CDR))
                                 (2 2 (:REWRITE DEFAULT-CAR)))
(RP::LIGTH-COMPRESS-S-C$FIX-PP-LST$FOR-S
     (158 3 (:REWRITE O<=-O-FINP-DEF))
     (68 4 (:REWRITE RP::MEASURE-LEMMA6))
     (22 22 (:REWRITE RP::CONS-COUNT-ATOM))
     (20 10 (:REWRITE DEFAULT-<-2))
     (20 10 (:REWRITE DEFAULT-<-1))
     (16 16 (:REWRITE DEFAULT-CDR))
     (16 8 (:REWRITE DEFAULT-+-2))
     (16 8 (:REWRITE DEFAULT-+-1))
     (15 3 (:REWRITE AC-<))
     (10 10
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
     (10 10
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (9 3 (:REWRITE O-INFP-O-FINP-O<=))
     (9 3 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
     (6 6
        (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
     (3 3 (:REWRITE RP::RP-EQUAL-REFLEXIVE)))
(RP::RP-TERM-LISTP-OF-LIGTH-COMPRESS-S-C$FIX-PP-LST$FOR-S.RES-PP1-LST
     (254 254 (:REWRITE DEFAULT-CDR))
     (70 70
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (47 47
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (16 8 (:REWRITE RP::RP-TERMP-CADR))
     (16 8 (:REWRITE RP::IS-IF-RP-TERMP)))
(RP::BOOLEANP-OF-LIGTH-COMPRESS-S-C$FIX-PP-LST$FOR-S.CHANGED
     (47 47 (:REWRITE DEFAULT-CDR)))
(RP::LIGHT-COMPRESS-S-C$FIX-PP$FOR-S)
(RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C$FIX-PP$FOR-S
     (11 11
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (5 5
        (:TYPE-PRESCRIPTION RP::LIGHT-COMPRESS-S-C$FIX-PP$FOR-S)))
(RP::LIGHT-COMPRESS-S-C$PASS-PP-LST
     (241 5 (:REWRITE O<=-O-FINP-DEF))
     (102 6 (:REWRITE RP::MEASURE-LEMMA6))
     (34 34 (:REWRITE RP::CONS-COUNT-ATOM))
     (28 14 (:REWRITE DEFAULT-<-2))
     (28 14 (:REWRITE DEFAULT-<-1))
     (26 13 (:REWRITE DEFAULT-+-2))
     (26 13 (:REWRITE DEFAULT-+-1))
     (25 5 (:REWRITE AC-<))
     (15 5 (:REWRITE O-INFP-O-FINP-O<=))
     (15 5 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
     (14 14
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
     (14 14
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (8 8
        (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
     (3 3 (:REWRITE RP::RP-EQUAL-REFLEXIVE)))
(RP::RP-TERM-LISTP-OF-LIGHT-COMPRESS-S-C$PASS-PP-LST.RES-PP1-LST
     (44 44 (:REWRITE DEFAULT-CDR))
     (24 24
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (12 12
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)))
(RP::RP-TERM-LISTP-OF-LIGHT-COMPRESS-S-C$PASS-PP-LST.RES-PP2-LST
     (82 82 (:REWRITE DEFAULT-CDR))
     (57 57
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (47 47
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (23 23
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)))
(RP::BOOLEANP-OF-LIGHT-COMPRESS-S-C$PASS-PP-LST.CHANGED
     (6 6 (:REWRITE DEFAULT-CDR)))
(RP::LIGHT-COMPRESS-S-C$PASS-PP)
(RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C$PASS-PP.RES-PP1
     (11 11
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C$PASS-PP.RES-PP2
     (26 26
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::BOOLEANP-OF-LIGHT-COMPRESS-S-C$PASS-PP.CHANGED)
(RP::O<-CHAIN (284 20 (:REWRITE O<=-O-FINP-DEF))
              (108 20 (:REWRITE O-FIRST-EXPT-<))
              (92 46 (:REWRITE DEFAULT-+-2))
              (92 46 (:REWRITE DEFAULT-+-1))
              (80 40 (:REWRITE DEFAULT-<-2))
              (80 40 (:REWRITE DEFAULT-<-1))
              (68 32 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
              (66 22
                  (:REWRITE |a < b & b < c  =>  a < c|))
              (66 22 (:REWRITE AC-<))
              (44 22 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
              (40 20 (:REWRITE O-INFP-O-FINP-O<=))
              (36 18 (:REWRITE O-FIRST-COEFF-<))
              (12 2 (:REWRITE O-P-O-INFP-CAR))
              (6 2 (:REWRITE O-P-DEF-O-FINP-1))
              (4 4 (:TYPE-PRESCRIPTION O-FINP))
              (4 4 (:REWRITE RP::LOCAL-MEASURE-LEMMA11))
              (2 2 (:REWRITE |~(a < a)|)))
(RP::O<-CHAIN-2 (379 22 (:REWRITE O<=-O-FINP-DEF))
                (304 244 (:REWRITE RP::MEASURE-LEMMA1))
                (141 41 (:REWRITE RP::CONS-COUNT-ATOM))
                (100 18 (:REWRITE O-FIRST-EXPT-<))
                (92 92 (:REWRITE RP::MEASURE-LEMMA1-2))
                (76 38 (:REWRITE DEFAULT-<-2))
                (73 38 (:REWRITE DEFAULT-<-1))
                (72 24
                    (:REWRITE |a < b & b < c  =>  a < c|))
                (69 24 (:REWRITE AC-<))
                (69 23 (:REWRITE RP::NOT-INCLUDE-RP))
                (64 32 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (63 3 (:REWRITE RP::LOCAL-MEASURE-LEMMA11))
                (46 46 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                (45 24 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                (41 22 (:REWRITE O-INFP-O-FINP-O<=))
                (38 38
                    (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                (38 38
                    (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                (36 6 (:REWRITE O-P-O-INFP-CAR))
                (32 16 (:REWRITE O-FIRST-COEFF-<))
                (30 6 (:REWRITE RP::MEASURE-LEMMA7-2))
                (30 6 (:REWRITE RP::MEASURE-LEMMA6-5))
                (20 20
                    (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                (18 6 (:REWRITE O-P-DEF-O-FINP-1))
                (18 6 (:REWRITE RP::MEASURE-LEMMA7))
                (12 12 (:TYPE-PRESCRIPTION O-FINP))
                (2 2 (:REWRITE |~(a < a)|)))
(RP::LIGHT-COMPRESS-S-C-AUX (64 60 (:REWRITE DEFAULT-CDR))
                            (26 18 (:REWRITE RP::CONS-COUNT-ATOM))
                            (24 24 (:REWRITE RP::MEASURE-LEMMA1))
                            (16 6 (:REWRITE RP::MEASURE-LEMMA1-2))
                            (15 1 (:REWRITE O-FINP-<))
                            (14 14 (:TYPE-PRESCRIPTION RP::CONS-COUNT))
                            (9 9 (:REWRITE DEFAULT-CAR))
                            (4 2 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                            (4 1 (:REWRITE O-P-O-INFP-CAR))
                            (3 1 (:REWRITE AC-<))
                            (2 1 (:REWRITE O-FIRST-EXPT-<))
                            (2 1 (:REWRITE DEFAULT-<-2))
                            (2 1 (:REWRITE DEFAULT-<-1))
                            (1 1 (:REWRITE |~(a < a)|))
                            (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                            (1 1 (:REWRITE O-P-DEF-O-FINP-1))
                            (1 1
                               (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                            (1 1
                               (:REWRITE RP::EQUALITY-MEASURE-LEMMA1)))
(RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C-AUX.PP-RES
     (227 227
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (220 4
          (:REWRITE RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C$PASS-PP.RES-PP2))
     (178 178 (:REWRITE DEFAULT-CDR))
     (136 24 (:REWRITE RP::IS-IF-RP-TERMP))
     (83 83 (:REWRITE DEFAULT-CAR))
     (48 8
         (:REWRITE RP::EXTRACT-FROM-RP-PSEUDO-TERM-LISTP))
     (36 36
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (32 16 (:REWRITE RP::RP-TERMP-CADR))
     (32 8
         (:REWRITE RP::RP-TERMP-EXTRACT-FROM-RP))
     (32 8 (:REWRITE RP::RP-TERMP-EX-FROM-RP))
     (24 4 (:REWRITE RP::RP-TERMP-CADDDR))
     (12 4 (:REWRITE RP::RP-TERMP-CADDR))
     (12 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP)))
(RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C-AUX.C-ARG-RES
     (137 137 (:REWRITE DEFAULT-CDR))
     (85 85 (:REWRITE DEFAULT-CAR))
     (49 15 (:REWRITE RP::IS-IF-RP-TERMP))
     (24 3 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (23 23
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (18 4
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::BOOLEANP-OF-LIGHT-COMPRESS-S-C-AUX.CHANGED
     (115 115 (:REWRITE DEFAULT-CDR))
     (53 53 (:REWRITE DEFAULT-CAR)))
(RP::LIGHT-COMPRESS-S-C (1 1
                           (:TYPE-PRESCRIPTION RP::LIGHT-COMPRESS-S-C)))
(RP::RP-TERMP-OF-LIGHT-COMPRESS-S-C
     (402 144 (:REWRITE RP::MEASURE-LEMMA1-2))
     (398 314 (:REWRITE DEFAULT-CDR))
     (383 378 (:REWRITE RP::MEASURE-LEMMA1))
     (100 96 (:REWRITE DEFAULT-CAR))
     (43 43
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (31 15 (:REWRITE RP::IS-IF-RP-TERMP))
     (25 7
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (24 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (18 18
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (11 11 (:REWRITE RP::EX-FROM-RP-X2))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (5 5
        (:TYPE-PRESCRIPTION RP::LIGHT-COMPRESS-S-C))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::|CASE-MATCH-('s & pp ('list single-c))$INLINE|)
(RP::|CASE-MATCH-('c & ''nil pp ('list single-c))$INLINE|)
(RP::|CASE-MATCH-('c & ''nil pp ''nil)$INLINE|)
(RP::DECOMPRESS-S-C-FN (75 75 (:REWRITE DEFAULT-CDR))
                       (19 19 (:REWRITE DEFAULT-CAR))
                       (8 2 (:REWRITE O-P-O-INFP-CAR))
                       (6 6 (:REWRITE |a < b & b < c  =>  a < c|))
                       (5 5 (:REWRITE DEFAULT-<-2))
                       (5 5 (:REWRITE DEFAULT-<-1))
                       (4 4 (:REWRITE O-INFP-O-FINP-O<=))
                       (2 2 (:REWRITE ZP-OPEN))
                       (2 2 (:REWRITE DEFAULT-+-2))
                       (2 2 (:REWRITE DEFAULT-+-1))
                       (2 2 (:REWRITE AC-<))
                       (1 1
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-TERMP-OF-DECOMPRESS-S-C
     (10734 10734 (:REWRITE DEFAULT-CDR))
     (2702 2702 (:REWRITE DEFAULT-CAR))
     (712 178 (:REWRITE O-P-O-INFP-CAR))
     (441 441
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (356 356 (:TYPE-PRESCRIPTION O-P))
     (294 87 (:REWRITE RP::IS-IF-RP-TERMP))
     (178 178 (:REWRITE O-P-DEF-O-FINP-1))
     (99 39
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (95 95
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (84 28 (:REWRITE FOLD-CONSTS-IN-+))
     (66 24 (:REWRITE ZP-OPEN))
     (60 27 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (59 59 (:REWRITE DEFAULT-+-2))
     (59 59 (:REWRITE DEFAULT-+-1))
     (42 42
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::NEGATE-LST-AUX (1 1
                       (:TYPE-PRESCRIPTION RP::NEGATE-LST-AUX)))
(RP::RP-TERM-LISTP-OF-NEGATE-LST-AUX
     (258 258 (:REWRITE DEFAULT-CAR))
     (200 40
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (175 175 (:REWRITE DEFAULT-CDR))
     (120 40
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (95 7 (:REWRITE RP::IS-IF-RP-TERMP))
     (56 56
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (40 40 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (30 12
         (:REWRITE RP::RP-TERMP-EXTRACT-FROM-RP))
     (30 12 (:REWRITE RP::RP-TERMP-EX-FROM-RP))
     (11 11
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (4 1
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::NEGATE-LST$INLINE)
(RP::RP-TERM-LISTP-OF-NEGATE-LST
     (3 3
        (:TYPE-PRESCRIPTION RP::NEGATE-LST$INLINE)))
(RP::NEGATE-LIST-INSTANCE$INLINE
     (3 3
        (:TYPE-PRESCRIPTION RP::NEGATE-LST$INLINE)))
(RP::RP-TERMP-OF-NEGATE-LIST-INSTANCE
     (7 7
        (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::C-PATTERN2-REDUCE)
(RP::RP-TERMP-OF-C-PATTERN2-REDUCE.S-RES
     (516 455 (:REWRITE DEFAULT-CDR))
     (197 186 (:REWRITE DEFAULT-CAR))
     (178 178
          (:TYPE-PRESCRIPTION RP::PP-SUM-MERGE))
     (156 10 (:REWRITE RP::IS-IF-RP-TERMP))
     (152 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (32 8 (:REWRITE O-P-O-INFP-CAR))
     (31 7
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (18 18
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (8 8 (:REWRITE O-P-DEF-O-FINP-1))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-TERMP-OF-C-PATTERN2-REDUCE.PP-RES
     (516 455 (:REWRITE DEFAULT-CDR))
     (183 174 (:REWRITE DEFAULT-CAR))
     (178 178
          (:TYPE-PRESCRIPTION RP::PP-SUM-MERGE))
     (160 10 (:REWRITE RP::IS-IF-RP-TERMP))
     (32 8 (:REWRITE O-P-O-INFP-CAR))
     (31 7
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (14 14
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (8 8 (:REWRITE O-P-DEF-O-FINP-1))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (6 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP)))
(RP::RP-TERMP-OF-C-PATTERN2-REDUCE.C-RES
     (333 296 (:REWRITE DEFAULT-CDR))
     (110 106 (:REWRITE DEFAULT-CAR))
     (96 96
         (:TYPE-PRESCRIPTION RP::PP-SUM-MERGE))
     (32 1 (:REWRITE RP::IS-IF-RP-TERMP))
     (24 6 (:REWRITE O-P-O-INFP-CAR))
     (13 3
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (12 2 (:REWRITE O-INFP->NEQ-0))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (6 6 (:REWRITE O-P-DEF-O-FINP-1))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (2 2
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)))
(RP::CREATE-C-INSTANCE (606 606 (:REWRITE DEFAULT-CDR))
                       (308 308 (:REWRITE DEFAULT-CAR))
                       (132 33 (:REWRITE O-P-O-INFP-CAR))
                       (66 66 (:TYPE-PRESCRIPTION O-P))
                       (33 33 (:REWRITE O-P-DEF-O-FINP-1))
                       (24 24 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-OF-CREATE-C-INSTANCE
     (2115 2115
           (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (593 515 (:REWRITE DEFAULT-CAR))
     (478 412 (:REWRITE DEFAULT-CDR))
     (333 42
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (164 28 (:REWRITE O-P-O-INFP-CAR))
     (144 12 (:REWRITE RP::F2-OF-BIT))
     (96 12 (:DEFINITION BITP))
     (80 28 (:REWRITE O-P-DEF-O-FINP-1))
     (52 52 (:TYPE-PRESCRIPTION O-FINP))
     (33 33 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (32 3
         (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (12 12 (:TYPE-PRESCRIPTION BITP))
     (10 10 (:REWRITE RP::SUM-COMM-1))
     (2 2 (:REWRITE RP::SUM-COMM-2)))
(RP::IS-RP-OF-BITP)
(RP::S-PATTERN3-REDUCE)
(RP::RP-TERMP-OF-S-PATTERN3-REDUCE.REDUCED
     (175 151 (:REWRITE DEFAULT-CDR))
     (96 91 (:REWRITE DEFAULT-CAR))
     (73 11 (:REWRITE RP::IS-IF-RP-TERMP))
     (16 4 (:REWRITE O-P-O-INFP-CAR))
     (13 13
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE O-INFP->NEQ-0))
     (9 2
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (5 3 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (4 4 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (4 4 (:REWRITE O-P-DEF-O-FINP-1))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::BOOLEANP-OF-S-PATTERN3-REDUCE.REDUCEDP
     (73 63 (:REWRITE DEFAULT-CDR))
     (23 22 (:REWRITE DEFAULT-CAR))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4 (:TYPE-PRESCRIPTION O-P))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::CREATE-S-INSTANCE$INLINE (220 220 (:REWRITE DEFAULT-CDR))
                              (122 122 (:REWRITE DEFAULT-CAR))
                              (40 10 (:REWRITE O-P-O-INFP-CAR))
                              (32 32 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                              (20 20 (:TYPE-PRESCRIPTION O-P))
                              (10 10 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::RP-TERMP-OF-CREATE-S-INSTANCE
     (255 249 (:REWRITE DEFAULT-CAR))
     (218 200 (:REWRITE DEFAULT-CDR))
     (66 6
         (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (38 7 (:REWRITE O-P-O-INFP-CAR))
     (17 7 (:REWRITE O-P-DEF-O-FINP-1))
     (10 10 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE RP::IS-IF-RP-TERMP))
     (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (6 6
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)))
(RP::SWAP-C-LSTS$INLINE)
(RP::RP-TERM-LISTP-OF-SWAP-C-LSTS.RES1)
(RP::RP-TERM-LISTP-OF-SWAP-C-LSTS.RES2)
(RP::LIGHT-S-OF-S-FIX-LST)
(RP::RP-TERM-LISTP-OF-LIGHT-S-OF-S-FIX-LST.PP-RES-LST
     (440 440 (:REWRITE DEFAULT-CDR))
     (371 371 (:REWRITE DEFAULT-CAR))
     (308 68
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (188 68
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (73 73
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (63 63
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (60 60 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (50 14 (:REWRITE RP::IS-IF-RP-TERMP))
     (50 7 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (18 6 (:REWRITE RP::RP-TERMP-CADR))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::RP-TERM-LISTP-OF-LIGHT-S-OF-S-FIX-LST.C-RES-LST
     (371 371 (:REWRITE DEFAULT-CDR))
     (286 286 (:REWRITE DEFAULT-CAR))
     (248 56
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (152 56
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (50 12 (:REWRITE RP::IS-IF-RP-TERMP))
     (48 48 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (15 15
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (14 14
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (12 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (9 3 (:REWRITE RP::RP-TERMP-CADR))
     (9 3 (:REWRITE RP::RP-TERMP-CADDR))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::LIGHT-S-OF-S-FIX)
(RP::RP-TERMP-OF-LIGHT-S-OF-S-FIX.PP-RES
     (30 30
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::RP-TERM-LISTP-OF-LIGHT-S-OF-S-FIX.C-RES-LST
     (18 18
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::SINGLE-C-TRY-MERGE-PARAMS-AUX$INLINE)
(RP::BOOLEANP-OF-SINGLE-C-TRY-MERGE-PARAMS-AUX)
(RP::SINGLE-C-TRY-MERGE-PARAMS)
(RP::RP-TERM-LISTP-OF-SINGLE-C-TRY-MERGE-PARAMS.UPDATED-S-LST
     (75 15
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (51 51 (:REWRITE DEFAULT-CAR))
     (45 15
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (45 15 (:DEFINITION QUOTEP))
     (31 31 (:REWRITE DEFAULT-CDR))
     (15 15 (:TYPE-PRESCRIPTION QUOTEP))
     (15 15 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (6 6
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)))
(RP::BOOLEANP-OF-SINGLE-C-TRY-MERGE-PARAMS.SUCCESS
     (14 14 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE DEFAULT-CDR)))
(RP::COUNT-C (588 572 (:REWRITE RP::MEASURE-LEMMA1))
             (420 166 (:REWRITE RP::MEASURE-LEMMA1-2))
             (240 164 (:REWRITE DEFAULT-CDR))
             (140 14
                  (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
             (75 47 (:REWRITE DEFAULT-CAR))
             (24 24 (:REWRITE RP::EX-FROM-RP-X2))
             (14 14 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
             (12 3 (:REWRITE O-P-O-INFP-CAR))
             (4 2 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
             (3 3 (:REWRITE O-P-DEF-O-FINP-1))
             (2 2 (:TYPE-PRESCRIPTION RP::CONS-COUNT)))
(RP::COUNT-C-FLAG (588 572 (:REWRITE RP::MEASURE-LEMMA1))
                  (420 166 (:REWRITE RP::MEASURE-LEMMA1-2))
                  (240 164 (:REWRITE DEFAULT-CDR))
                  (140 14
                       (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
                  (75 47 (:REWRITE DEFAULT-CAR))
                  (24 24 (:REWRITE RP::EX-FROM-RP-X2))
                  (14 14 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                  (12 3 (:REWRITE O-P-O-INFP-CAR))
                  (4 2 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                  (3 3 (:REWRITE O-P-DEF-O-FINP-1))
                  (2 2 (:TYPE-PRESCRIPTION RP::CONS-COUNT)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::COUNT-C-FLAG-EQUIVALENCES)
(RP::C-SUM-MERGE-M-LEMMA1 (64 64 (:REWRITE DEFAULT-CAR))
                          (44 44 (:REWRITE DEFAULT-CDR))
                          (32 8 (:REWRITE O-P-O-INFP-CAR))
                          (20 4 (:DEFINITION LEN))
                          (20 2 (:REWRITE LEN-WHEN-PREFIXP))
                          (16 16 (:TYPE-PRESCRIPTION O-P))
                          (16 4 (:DEFINITION NFIX))
                          (12 8 (:REWRITE DEFAULT-<-2))
                          (12 8 (:REWRITE DEFAULT-<-1))
                          (12 6 (:REWRITE DEFAULT-+-2))
                          (8 8 (:REWRITE O-P-DEF-O-FINP-1))
                          (8 6 (:REWRITE DEFAULT-+-1))
                          (4 4 (:TYPE-PRESCRIPTION PREFIXP))
                          (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                          (4 4
                             (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                          (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                          (2 2
                             (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                          (2 2
                             (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                          (2 2 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                          (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                          (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                          (2 2
                             (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                          (2 2
                             (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(RP::C-SUM-MERGE-M-LEMMA2 (831 831 (:REWRITE DEFAULT-CDR))
                          (262 246 (:REWRITE DEFAULT-CAR))
                          (90 18 (:REWRITE RP::IFIX-OPENER))
                          (54 18
                              (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                          (40 10 (:REWRITE O-P-O-INFP-CAR))
                          (36 36 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                          (32 16 (:REWRITE DEFAULT-+-2))
                          (22 16 (:REWRITE DEFAULT-+-1))
                          (18 18
                              (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                          (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                          (7 3 (:REWRITE DEFAULT-<-2))
                          (7 3 (:REWRITE DEFAULT-<-1))
                          (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::C-SUM-MERGE-M-LEMMA3 (8 4 (:REWRITE DEFAULT-+-2))
                          (8 4 (:REWRITE DEFAULT-+-1))
                          (6 2 (:REWRITE DEFAULT-<-1))
                          (4 4 (:REWRITE DEFAULT-CDR))
                          (4 2 (:REWRITE DEFAULT-<-2))
                          (2 2 (:REWRITE DEFAULT-CAR)))
(RP::C-SUM-MERGE-M-LEMMA4
     (13 5 (:REWRITE DEFAULT-+-2))
     (11 5 (:REWRITE DEFAULT-+-1))
     (3 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (3 1 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 1 (:REWRITE DEFAULT-<-2))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE DEFAULT-CDR)))
(RP::C-SUM-MERGE-M-LEMMA5 (4 2 (:REWRITE DEFAULT-+-2))
                          (4 2 (:REWRITE DEFAULT-+-1))
                          (3 1 (:REWRITE DEFAULT-<-2))
                          (3 1 (:REWRITE DEFAULT-<-1))
                          (1 1 (:REWRITE DEFAULT-CAR)))
(RP::C-SUM-MERGE-M-LEMMA6 (40 2 (:REWRITE RP::C-SUM-MERGE-M-LEMMA5))
                          (10 5 (:REWRITE DEFAULT-+-2))
                          (10 5 (:REWRITE DEFAULT-+-1))
                          (6 2 (:REWRITE DEFAULT-<-1))
                          (5 2 (:REWRITE DEFAULT-<-2))
                          (3 3 (:REWRITE DEFAULT-CAR))
                          (1 1 (:REWRITE DEFAULT-CDR)))
(RP::C-SUM-MERGE-M-LEMMA7 (2 1 (:REWRITE DEFAULT-<-2))
                          (2 1 (:REWRITE DEFAULT-<-1))
                          (1 1 (:REWRITE DEFAULT-CAR)))
(RP::C-SUM-MERGE-M-LEMMA8 (80 4 (:REWRITE RP::C-SUM-MERGE-M-LEMMA5))
                          (20 10 (:REWRITE DEFAULT-+-2))
                          (20 10 (:REWRITE DEFAULT-+-1))
                          (9 3 (:REWRITE DEFAULT-<-2))
                          (8 3 (:REWRITE DEFAULT-<-1))
                          (4 4 (:REWRITE DEFAULT-CDR))
                          (4 4 (:REWRITE DEFAULT-CAR)))
(RP::NEGATED-TERMP$INLINE)
(RP::SINGLE-C-TRY-MERGE
     (1880 2
           (:REWRITE RP::SUM-WITH-POSITIVE-LEMMA3))
     (1824 4 (:LINEAR ACL2-COUNT-OF-SUM))
     (872 306 (:REWRITE DEFAULT-+-2))
     (770 770 (:REWRITE RP::MEASURE-LEMMA1))
     (644 28 (:DEFINITION LENGTH))
     (560 306 (:REWRITE DEFAULT-+-1))
     (532 28 (:DEFINITION LEN))
     (394 394
          (:TYPE-PRESCRIPTION ACL2-COUNT-OF-CONSP-POSITIVE))
     (393 165 (:REWRITE DEFAULT-CDR))
     (392 56 (:DEFINITION INTEGER-ABS))
     (388 192 (:REWRITE DEFAULT-<-1))
     (364 144 (:REWRITE RP::MEASURE-LEMMA1-2))
     (284 192 (:REWRITE DEFAULT-<-2))
     (272 18
          (:REWRITE RP::EQUALITY-MEASURE-LEMMA7))
     (231 18
          (:REWRITE RP::EQUALITY-MEASURE-LEMMA8))
     (221 18
          (:REWRITE RP::EQUALITY-MEASURE-LEMMA6))
     (192 192
          (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (177 149
          (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (136 136 (:REWRITE DEFAULT-CAR))
     (125 25 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
     (84 84
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (84 56 (:REWRITE STR::CONSP-OF-EXPLODE))
     (75 75
         (:TYPE-PRESCRIPTION NAT-LIST-MEASURE))
     (71 71 (:REWRITE FOLD-CONSTS-IN-+))
     (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
     (56 28
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (53 53
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (40 10 (:REWRITE O-P-O-INFP-CAR))
     (28 28 (:TYPE-PRESCRIPTION LEN))
     (28 28
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (28 28 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (28 28 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (28 28
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (28 28
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (28 28 (:REWRITE DEFAULT-REALPART))
     (28 28 (:REWRITE DEFAULT-NUMERATOR))
     (28 28 (:REWRITE DEFAULT-IMAGPART))
     (28 28 (:REWRITE DEFAULT-DENOMINATOR))
     (10 10 (:REWRITE O-P-DEF-O-FINP-1))
     (10 2
         (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
     (6 6
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (4 4
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (4 4
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (1 1 (:REWRITE RP::C-SUM-MERGE-M-LEMMA3)))
(RP::C-SUM-MERGE-FLAG (1880 2
                            (:REWRITE RP::SUM-WITH-POSITIVE-LEMMA3))
                      (1824 4 (:LINEAR ACL2-COUNT-OF-SUM))
                      (874 308 (:REWRITE DEFAULT-+-2))
                      (768 768 (:REWRITE RP::MEASURE-LEMMA1))
                      (644 28 (:DEFINITION LENGTH))
                      (562 308 (:REWRITE DEFAULT-+-1))
                      (532 28 (:DEFINITION LEN))
                      (394 394
                           (:TYPE-PRESCRIPTION ACL2-COUNT-OF-CONSP-POSITIVE))
                      (393 165 (:REWRITE DEFAULT-CDR))
                      (392 56 (:DEFINITION INTEGER-ABS))
                      (378 189 (:REWRITE DEFAULT-<-1))
                      (364 144 (:REWRITE RP::MEASURE-LEMMA1-2))
                      (278 189 (:REWRITE DEFAULT-<-2))
                      (255 17
                           (:REWRITE RP::EQUALITY-MEASURE-LEMMA7))
                      (217 17
                           (:REWRITE RP::EQUALITY-MEASURE-LEMMA8))
                      (208 17
                           (:REWRITE RP::EQUALITY-MEASURE-LEMMA6))
                      (189 189
                           (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                      (177 149
                           (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                      (136 136 (:REWRITE DEFAULT-CAR))
                      (125 25 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                      (84 84
                          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                      (84 56 (:REWRITE STR::CONSP-OF-EXPLODE))
                      (75 75
                          (:TYPE-PRESCRIPTION NAT-LIST-MEASURE))
                      (71 71 (:REWRITE FOLD-CONSTS-IN-+))
                      (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
                      (56 28
                          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                      (53 53
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (40 10 (:REWRITE O-P-O-INFP-CAR))
                      (28 28 (:TYPE-PRESCRIPTION LEN))
                      (28 28
                          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                      (28 28 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                      (28 28 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                      (28 28
                          (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                      (28 28
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                      (28 28 (:REWRITE DEFAULT-REALPART))
                      (28 28 (:REWRITE DEFAULT-NUMERATOR))
                      (28 28 (:REWRITE DEFAULT-IMAGPART))
                      (28 28 (:REWRITE DEFAULT-DENOMINATOR))
                      (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                      (10 2
                          (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
                      (6 6
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                      (4 4 (:TYPE-PRESCRIPTION RP::S-SUM-MERGE))
                      (4 4
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                      (4 4
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                      (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                      (2 2
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                      (1 1 (:REWRITE RP::C-SUM-MERGE-M-LEMMA3)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::C-SUM-MERGE-FLAG-EQUIVALENCES)
(RP::FLAG-LEMMA-FOR-RETURN-TYPE-OF-SINGLE-C-TRY-MERGE.COUGHED-S
     (16404 16404 (:REWRITE DEFAULT-CAR))
     (10065 3000
            (:REWRITE RP::C-SUM-MERGE-M-LEMMA8))
     (9820 9820 (:REWRITE DEFAULT-CDR))
     (5463 1823
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2529 1000 (:REWRITE DEFAULT-<-1))
     (2493 1000 (:REWRITE DEFAULT-<-2))
     (2118 1059 (:REWRITE DEFAULT-+-2))
     (2118 1059 (:REWRITE DEFAULT-+-1))
     (1976 1976
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1860 1860 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1 1 (:REWRITE CDR-CONS)))
(RP::RETURN-TYPE-OF-SINGLE-C-TRY-MERGE.COUGHED-S)
(RP::RETURN-TYPE-OF-SINGLE-C-TRY-MERGE.COUGHED-PP-LST)
(RP::RETURN-TYPE-OF-SINGLE-C-TRY-MERGE.PRODUCED-C-LST)
(RP::RETURN-TYPE-OF-SINGLE-C-TRY-MERGE.MERGE-SUCCESS)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-AUX.COUGHED-S)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-AUX.COUGHED-PP-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-AUX.PRODUCED-C-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-AUX.UPDATED-C2-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-AUX.MERGE-SUCCESS)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST.COUGHED-S)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST.COUGHED-PP-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST.NEW-C2-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-LST.COUGHED-S)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-LST.COUGHED-PP-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-LST-LST.UPDATED-C2-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE.COUGHED-S)
(RP::RETURN-TYPE-OF-C-SUM-MERGE.COUGHED-PP-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE.C-MERGED-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE.TO-BE-COUGHED-C-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-AUX.COUGHED-S)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-AUX.COUGHED-PP-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-AUX.C-MERGED-LST)
(RP::RETURN-TYPE-OF-C-SUM-MERGE-AUX.TO-BE-COUGHED-C-LST)
(RP::RP-TERMP-LEMMA1 (2 2
                        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                     (2 2 (:REWRITE DEFAULT-CAR)))
(RP::S-OF-S-FIX-LST-FN (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
                       (3 3 (:REWRITE DEFAULT-<-2))
                       (3 3 (:REWRITE DEFAULT-<-1))
                       (2 2 (:REWRITE O-INFP-O-FINP-O<=))
                       (1 1 (:REWRITE ZP-OPEN))
                       (1 1
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (1 1 (:REWRITE DEFAULT-+-2))
                       (1 1 (:REWRITE DEFAULT-+-1))
                       (1 1 (:REWRITE AC-<)))
(RP::RP-TERM-LISTP-OF-S-OF-S-FIX-LST
     (2160 2160 (:REWRITE DEFAULT-CDR))
     (1234 1234 (:REWRITE DEFAULT-CAR))
     (516 172 (:REWRITE FOLD-CONSTS-IN-+))
     (373 115 (:REWRITE ZP-OPEN))
     (360 66
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (308 88 (:REWRITE RP::IS-IF-RP-TERMP))
     (268 268 (:REWRITE DEFAULT-+-2))
     (268 268 (:REWRITE DEFAULT-+-1))
     (180 66
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (148 32 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (96 96
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (86 86 (:REWRITE DEFAULT-<-2))
     (86 86 (:REWRITE DEFAULT-<-1))
     (66 22
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (57 57 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (44 44
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (44 44 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::S-OF-S-FIX)
(RP::RP-TERMP-OF-S-OF-S-FIX.PP-RES
     (30 30
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::RP-TERM-LISTP-OF-S-OF-S-FIX.C-RES-LST
     (18 18
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::QUOTE-ALL)
(RP::RP-TERM-LISTP-OF-QUOTE-ALL (4 4 (:REWRITE DEFAULT-CDR))
                                (2 2 (:REWRITE DEFAULT-CAR)))
(RP::GOOD-4VEC-TERM-P (611 596 (:REWRITE RP::MEASURE-LEMMA1))
                      (589 204 (:REWRITE RP::MEASURE-LEMMA1-2))
                      (319 213 (:REWRITE DEFAULT-CDR))
                      (182 62 (:REWRITE RP::CONS-COUNT-ATOM))
                      (164 6 (:REWRITE O<=-O-FINP-DEF))
                      (76 12 (:REWRITE RP::MEASURE-LEMMA7-2))
                      (60 15 (:REWRITE O-P-O-INFP-CAR))
                      (40 40 (:REWRITE DEFAULT-CAR))
                      (30 30 (:REWRITE RP::EX-FROM-RP-X2))
                      (30 15 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                      (28 28
                          (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                      (18 6 (:REWRITE AC-<))
                      (16 16
                          (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                      (15 15 (:REWRITE O-P-DEF-O-FINP-1))
                      (12 6 (:REWRITE O-INFP-O-FINP-O<=))
                      (8 4 (:REWRITE DEFAULT-<-2))
                      (8 4 (:REWRITE DEFAULT-<-1))
                      (6 6 (:REWRITE |a < b & b < c  =>  a < c|))
                      (4 4
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1)))
(RP::4VEC->PP-TERM (3385 3279 (:REWRITE DEFAULT-CDR))
                   (848 848 (:REWRITE DEFAULT-CAR))
                   (611 596 (:REWRITE RP::MEASURE-LEMMA1))
                   (589 204 (:REWRITE RP::MEASURE-LEMMA1-2))
                   (188 47 (:REWRITE O-P-O-INFP-CAR))
                   (182 62 (:REWRITE RP::CONS-COUNT-ATOM))
                   (164 6 (:REWRITE O<=-O-FINP-DEF))
                   (112 16 (:DEFINITION NATP))
                   (76 12 (:REWRITE RP::MEASURE-LEMMA7-2))
                   (48 16
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (47 47 (:REWRITE O-P-DEF-O-FINP-1))
                   (32 32 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (30 30 (:REWRITE RP::EX-FROM-RP-X2))
                   (30 15 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                   (28 28
                       (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                   (24 20 (:REWRITE DEFAULT-<-2))
                   (24 20 (:REWRITE DEFAULT-<-1))
                   (18 6 (:REWRITE AC-<))
                   (16 16
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (16 16 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (16 16
                       (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                   (12 6 (:REWRITE O-INFP-O-FINP-O<=))
                   (6 6 (:REWRITE |a < b & b < c  =>  a < c|))
                   (4 4
                      (:REWRITE RP::EQUALITY-MEASURE-LEMMA1)))
(RP::RP-TERMP-OF--4VEC->PP-TERM
     (16098 16098 (:REWRITE DEFAULT-CDR))
     (6209 6209 (:REWRITE DEFAULT-CAR))
     (2109 2109
           (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (78 20 (:REWRITE RP::IS-IF-RP-TERMP))
     (65 17
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (62 9 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (27 27
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (27 9
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (6 2
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (4 4 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::PP-TERM-P-OF--4VEC->PP-TERM
     (43519 43187 (:REWRITE DEFAULT-CDR))
     (17694 17694 (:REWRITE DEFAULT-CAR))
     (13920 4640 (:REWRITE RP::NOT-INCLUDE-RP))
     (9280 9280
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (4633 4633
           (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (668 167 (:REWRITE O-P-O-INFP-CAR))
     (167 167 (:REWRITE O-P-DEF-O-FINP-1))
     (126 42
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (84 84 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (42 42
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (42 42 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (42 42 (:REWRITE DEFAULT-<-2))
     (42 42 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERM-LISTP-OF-APPEND)
(RP::RP-TERM-LISTP-OF-REPEAT
     (28 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (18 2 (:DEFINITION QUOTEP))
     (12 2
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (11 11
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (10 4 (:REWRITE DEFAULT-CAR))
     (8 2 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2 (:TYPE-PRESCRIPTION QUOTEP))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1 1
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1 1 (:REWRITE REPEAT-WHEN-ZP)))
(RP::EXTRACT-NEW-SUM-ELEMENT (24 8 (:REWRITE RP::CONS-COUNT-ATOM))
                             (22 1 (:REWRITE O<=-O-FINP-DEF))
                             (8 8 (:REWRITE RP::MEASURE-LEMMA1))
                             (8 2 (:REWRITE O-P-O-INFP-CAR))
                             (6 6 (:REWRITE DEFAULT-CDR))
                             (4 4
                                (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                             (4 2 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                             (3 1 (:REWRITE AC-<))
                             (2 2 (:REWRITE O-P-DEF-O-FINP-1))
                             (2 2 (:REWRITE RP::MEASURE-LEMMA7-2))
                             (2 2
                                (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                             (2 2 (:REWRITE DEFAULT-CAR))
                             (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                             (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                             (1 1 (:REWRITE RP::MEASURE-LEMMA-LOOSE1)))
(RP::RP-TERM-LISTP-OF-EXTRACT-NEW-SUM-ELEMENT
     (365 365
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (56 56
         (:TYPE-PRESCRIPTION RP::EXTRACT-NEW-SUM-ELEMENT))
     (45 9 (:REWRITE RP::IFIX-OPENER))
     (37 2 (:DEFINITION BINARY-APPEND))
     (27 21 (:REWRITE DEFAULT-CAR))
     (27 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (24 18 (:REWRITE DEFAULT-CDR))
     (24 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (23 8 (:REWRITE CONSP-OF-REPEAT))
     (20 20 (:TYPE-PRESCRIPTION REPEAT))
     (20 13 (:REWRITE DEFAULT-<-1))
     (18 18 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (15 3 (:REWRITE ZP-OPEN))
     (13 13 (:REWRITE DEFAULT-<-2))
     (11 2 (:REWRITE REPEAT-WHEN-ZP))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 2
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (8 2 (:REWRITE RP::IS-IF-RP-TERMP))
     (8 1 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (3 3
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (3 1
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (1 1 (:TYPE-PRESCRIPTION ZP))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::EXTRACT-NEW-SUM-CONSED (313 18 (:DEFINITION RP::EX-FROM-RP))
                            (235 116 (:REWRITE RP::MEASURE-LEMMA1))
                            (233 80 (:REWRITE RP::MEASURE-LEMMA1-2))
                            (154 55 (:REWRITE DEFAULT-CDR))
                            (80 17 (:REWRITE DEFAULT-CAR))
                            (63 21 (:REWRITE RP::NOT-INCLUDE-RP))
                            (42 42 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                            (39 39
                                (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                            (36 2 (:REWRITE RP::EX-FROM-RP-X2))
                            (22 1 (:REWRITE O<=-O-FINP-DEF))
                            (14 6 (:REWRITE RP::CONS-COUNT-ATOM))
                            (4 4
                               (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                            (4 1 (:REWRITE O-P-O-INFP-CAR))
                            (3 1 (:REWRITE AC-<))
                            (2 2 (:REWRITE RP::MEASURE-LEMMA7-2))
                            (2 2
                               (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                            (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                            (2 1 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
                            (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                            (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::RP-TERM-LISTP-OF-EXTRACT-NEW-SUM-CONSED
     (624 208 (:REWRITE RP::NOT-INCLUDE-RP))
     (416 416
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (381 381
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (32 8 (:REWRITE O-P-O-INFP-CAR))
     (28 28 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 8 (:REWRITE O-P-DEF-O-FINP-1))
     (8 2
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (8 2 (:REWRITE RP::IS-IF-RP-TERMP))
     (8 1 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (3 3
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (3 1
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::NEW-SUM-MERGE-AUX-DISSECT-TERM$INLINE)
(RP::RP-TERMP-OF-NEW-SUM-MERGE-AUX-DISSECT-TERM.TERM-ORIG
     (11 11 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR)))
(RP::RP-TERMP-OF-NEW-SUM-MERGE-AUX-DISSECT-TERM.ABS-TERM-W/-SC
     (11 11 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR)))
(RP::RP-TERMP-OF-NEW-SUM-MERGE-AUX-DISSECT-TERM.ABS-TERM
     (11 11 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR)))
(RP::BOOLEANP-OF-NEW-SUM-MERGE-AUX-DISSECT-TERM.NEGATED
     (11 11 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR)))
(RP::NEW-SUM-MERGE-AUX-ADD-NEGATED-COUGHED$INLINE)
(RP::RP-TERM-LISTP-OF-NEW-SUM-MERGE-AUX-ADD-NEGATED-COUGHED
     (12 12
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (4 4 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE DEFAULT-CDR)))
(RP::NEW-SUM-MERGE-AUX (1 1
                          (:TYPE-PRESCRIPTION RP::NEGATE-LST$INLINE)))
(RP::RETURN-VALS--OF--NEW-SUM-MERGE-AUX
     (105 35 (:REWRITE RP::IS-IF-RP-TERMP))
     (36 36
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (35 12 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (3 3 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::NEW-SUM-MERGE)
(RP::RETURN-VALS--OF--NEW-SUM-MERGE
     (7 7
        (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::WELL-FORMED-NEW-SUM
     (3677 3 (:REWRITE O<=-O-FINP-DEF))
     (1639 562 (:REWRITE DEFAULT-+-2))
     (956 562 (:REWRITE DEFAULT-+-1))
     (645 43 (:DEFINITION LENGTH))
     (473 43 (:DEFINITION LEN))
     (379 250 (:REWRITE DEFAULT-CDR))
     (344 86 (:DEFINITION INTEGER-ABS))
     (200 50 (:REWRITE O-P-O-INFP-CAR))
     (162 162 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (156 156 (:REWRITE DEFAULT-CAR))
     (129 129
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (129 86 (:REWRITE STR::CONSP-OF-EXPLODE))
     (129 43
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (124 124 (:REWRITE FOLD-CONSTS-IN-+))
     (114 38
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (101 91 (:REWRITE DEFAULT-<-2))
     (101 91 (:REWRITE DEFAULT-<-1))
     (86 86 (:REWRITE DEFAULT-UNARY-MINUS))
     (86 43
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (63 63
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (50 50 (:REWRITE O-P-DEF-O-FINP-1))
     (43 43 (:TYPE-PRESCRIPTION LEN))
     (43 43
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (43 43 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (43 43 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (43 43
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (43 43
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (43 43
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (43 43 (:REWRITE DEFAULT-REALPART))
     (43 43 (:REWRITE DEFAULT-NUMERATOR))
     (43 43 (:REWRITE DEFAULT-IMAGPART))
     (43 43 (:REWRITE DEFAULT-DENOMINATOR))
     (43 43
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (28 28
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (22 22
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (16 2 (:REWRITE O-FIRST-EXPT-<))
     (15 3 (:REWRITE AC-<))
     (12 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (9 3 (:REWRITE O-INFP-O-FINP-O<=))
     (9 3 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
     (6 2 (:REWRITE O-FIRST-COEFF-<))
     (3 3
        (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::BOOLEANP-OF-WELL-FORMED-NEW-SUM)
(RP::LIGHT-PP-TERM-P$INLINE)
(RP::LIGHT-PP-TERM-LIST-P)
(RP::LEMMA1 (28 4
                (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
            (22 22 (:TYPE-PRESCRIPTION RP::--))
            (6 6 (:REWRITE DEFAULT-CDR))
            (6 6 (:REWRITE DEFAULT-CAR))
            (2 2 (:REWRITE DEFAULT-+-2))
            (2 2 (:REWRITE DEFAULT-+-1))
            (2 1 (:TYPE-PRESCRIPTION RP::LEMMA1)))
(RP::QUARTERNARYP-SUM-AUX
     (3677 3 (:REWRITE O<=-O-FINP-DEF))
     (1639 562 (:REWRITE DEFAULT-+-2))
     (956 562 (:REWRITE DEFAULT-+-1))
     (645 43 (:DEFINITION LENGTH))
     (473 43 (:DEFINITION LEN))
     (379 250 (:REWRITE DEFAULT-CDR))
     (344 86 (:DEFINITION INTEGER-ABS))
     (200 50 (:REWRITE O-P-O-INFP-CAR))
     (162 162 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (156 156 (:REWRITE DEFAULT-CAR))
     (129 129
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (129 86 (:REWRITE STR::CONSP-OF-EXPLODE))
     (129 43
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (124 124 (:REWRITE FOLD-CONSTS-IN-+))
     (114 38
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (101 91 (:REWRITE DEFAULT-<-2))
     (101 91 (:REWRITE DEFAULT-<-1))
     (86 86 (:REWRITE DEFAULT-UNARY-MINUS))
     (86 43
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (63 63
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (50 50 (:REWRITE O-P-DEF-O-FINP-1))
     (43 43
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (43 43 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (43 43 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (43 43
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (43 43
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (43 43
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (43 43 (:REWRITE DEFAULT-REALPART))
     (43 43 (:REWRITE DEFAULT-NUMERATOR))
     (43 43 (:REWRITE DEFAULT-IMAGPART))
     (43 43 (:REWRITE DEFAULT-DENOMINATOR))
     (43 43
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (28 28
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (22 22
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (16 2 (:REWRITE O-FIRST-EXPT-<))
     (15 3 (:REWRITE AC-<))
     (12 6 (:TYPE-PRESCRIPTION RP::LEMMA1))
     (12 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (9 3 (:REWRITE O-INFP-O-FINP-O<=))
     (9 3 (:REWRITE RP::LOCAL-MEASURE-LEMMA4))
     (6 6 (:TYPE-PRESCRIPTION NAT-LISTP))
     (6 2 (:REWRITE O-FIRST-COEFF-<))
     (3 3
        (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::NATP-OF-QUARTERNARYP-SUM-AUX.RES
     (364 182 (:TYPE-PRESCRIPTION RP::LEMMA1))
     (222 222 (:TYPE-PRESCRIPTION NAT-LISTP))
     (112 8 (:REWRITE RP::LEMMA1))
     (88 8 (:DEFINITION NAT-LISTP))
     (32 8 (:REWRITE O-P-O-INFP-CAR))
     (27 27 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 8 (:REWRITE O-P-DEF-O-FINP-1))
     (8 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (5 1 (:DEFINITION LEN))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::BOOLEANP-OF-QUARTERNARYP-SUM-AUX.VALID
     (364 182 (:TYPE-PRESCRIPTION RP::LEMMA1))
     (222 222 (:TYPE-PRESCRIPTION NAT-LISTP))
     (112 8 (:REWRITE RP::LEMMA1))
     (88 8 (:DEFINITION NAT-LISTP))
     (32 8 (:REWRITE O-P-O-INFP-CAR))
     (27 27 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (12 6 (:REWRITE DEFAULT-+-2))
     (8 8 (:REWRITE O-P-DEF-O-FINP-1))
     (7 6 (:REWRITE DEFAULT-+-1))
     (5 5
        (:TYPE-PRESCRIPTION RP::NATP-OF-QUARTERNARYP-SUM-AUX.RES))
     (5 1 (:DEFINITION LEN))
     (2 2 (:TYPE-PRESCRIPTION LEN))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::QUARTERNARYP-SUM-AUX)
(RP::QUARTERNARYP-SUM)
(RP::BOOLEANP-OF-QUARTERNARYP-SUM)
(RP::C-SPEC-META-AUX)
(RP::RP-TERMP-OF-C-SPEC-META-AUX (173 173
                                      (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                                 (103 97 (:REWRITE DEFAULT-CAR))
                                 (28 28 (:REWRITE DEFAULT-CDR))
                                 (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::S-SPEC-META-AUX)
(RP::RP-TERMP-OF-S-SPEC-META-AUX (21 21
                                     (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::LEMMA1)
(RP::S-C-SPEC-META)
(RP::RP-TERMP-OF-S-C-SPEC-META.RES (60 60 (:REWRITE DEFAULT-CDR))
                                   (60 60 (:REWRITE DEFAULT-CAR)))
(RP::DONT-RW-SYNTAXP-OF-S-C-SPEC-META.DONT-RW)
(RP::MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-ATOM-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-ENDP-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-APPEND-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-IFIX-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA----WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-SUM-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-SUM-LIST-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BIT-FIX-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-AND-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-AND-LIST-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-SORT-SUM-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-=-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-NFIX-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-NONNEGATIVE-INTEGER-QUOTIENT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-FLOOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-C-SPEC-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-MOD-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-S-SPEC-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-C-S-SPEC-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-S-C-SPEC-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-ZIP-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-FIX-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-EXPT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-EVENP-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-ODDP-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGBITP-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGBIT$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BIT-OF-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC->UPPER$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC->LOWER$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-2VEC-P$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-2VEC->VAL$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-EQL-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-PAIRLIS2-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-FMT-TO-COMMENT-WINDOW-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BREAK$-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-CHECK-DCL-GUARDIAN-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LIFIX$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-2VEC$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-ASH-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-SHIFT-CORE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-RSH-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-THE-CHECK-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-LOGAND-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-EXPT2$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-IMOD$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGHEAD$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGAPP-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-CONCAT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-ZERO-EXT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-PART-SELECT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BITS-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGNOT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGANDC2-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-P-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-LOGIOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-FIX-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-BITAND-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-BITAND-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-BITOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-BITOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-FIX$INLINE-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-?-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-?-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-LOGORC1-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-LOGEQV-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-LOGXOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-?*-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-?*-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-BITXOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-3VEC-BITNOT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-BITNOT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-4VEC-BITNOT$-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-ADDER-B+-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-S-OF-C-TRIG-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-?-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-XOR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-OR-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-BINARY-NOT-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-C-RES-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-C-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-M2-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-F2-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-TIMES2-WHEN-MULT-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-S-WHEN-MULT-FORMULA-CHECKS)
(RP::RP-EVL-OF-ATOM-WHEN-MULT-FORMULA-CHECKS
     (266 266 (:REWRITE DEFAULT-CAR))
     (122 19 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (87 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (69 69 (:REWRITE DEFAULT-CDR))
     (29 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 19 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (27 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (26 16 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (26 16 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (24 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (9 9
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::RP-EVL-OF-ATOM-WHEN-MV-NTH-FORMULA-CHECKS))
     (6 6
        (:REWRITE RP::RP-EVL-OF-ATOM-WHEN-HONS-GET-META-FORMULA-CHECKS))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-ENDP-WHEN-MULT-FORMULA-CHECKS
     (162 162 (:REWRITE DEFAULT-CAR))
     (79 12 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (46 46 (:REWRITE DEFAULT-CDR))
     (18 12 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (17 11 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::RP-EVL-OF-ENDP-WHEN-HONS-GET-META-FORMULA-CHECKS))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-BINARY-APPEND-LEMMA
     (479 476 (:REWRITE DEFAULT-CAR))
     (208 104
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (162 42 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (104 104 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (104 104 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (95 92 (:REWRITE DEFAULT-CDR))
     (84 13 (:DEFINITION RP::IS-SYNP$INLINE))
     (58 42 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (56 40 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (56 40 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (56 40
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (55 39
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (55 39 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (53 37 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (53 37 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (51 35 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (51 35 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (36 36
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (36 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (21 21
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-BINARY-APPEND-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (90 45
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (45 45 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (45 45 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (27 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (27 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP)))
(RP::RP-EVL-OF-IFIX-WHEN-MULT-FORMULA-CHECKS
     (269 269 (:REWRITE DEFAULT-CAR))
     (125 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (87 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (31 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (29 19 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (29 19 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (24 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (88 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (24 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-BINARY-SUM-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (134 37 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 4 (:REWRITE RP::IFIX-OPENER))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE DEFAULT-+-2))
     (4 2 (:REWRITE DEFAULT-+-1)))
(RP::RP-EVL-OF-SUM-LIST-LEMMA
     (447 447 (:REWRITE DEFAULT-CAR))
     (160 41 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (84 13 (:DEFINITION RP::IS-SYNP$INLINE))
     (78 78 (:REWRITE DEFAULT-CDR))
     (70 10
         (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (57 41 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (57 41
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (57 41 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (55 39 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (55 39 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (55 39
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (55 39
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (55 39 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (55 39 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (53 37 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (53 37 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 42 (:TYPE-PRESCRIPTION RP::--))
     (36 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (35 35
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (25 25
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::RP-EVL-OF-SUM-LIST-WHEN-MULT-FORMULA-CHECKS
     (159 159 (:REWRITE DEFAULT-CAR))
     (77 11 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (45 45 (:REWRITE DEFAULT-CDR))
     (17 11 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (17 11
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (17 11
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (17 11
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (9 9
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-BIT-FIX-WHEN-MULT-FORMULA-CHECKS
     (281 281 (:REWRITE DEFAULT-CAR))
     (177 30 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (123 14 (:DEFINITION RP::IS-SYNP$INLINE))
     (106 106 (:REWRITE DEFAULT-CDR))
     (40 30
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (40 30 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (40 30 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (40 30 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (40 30
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (39 29
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (39 29 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (38 28 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (38 28 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (30 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 9
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::RP-EVL-OF-BINARY-AND-WHEN-MULT-FORMULA-CHECKS
     (406 406 (:REWRITE DEFAULT-CAR))
     (286 63 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (189 21 (:DEFINITION RP::IS-SYNP$INLINE))
     (171 171 (:REWRITE DEFAULT-CDR))
     (77 63 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (75 61 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (75 61 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (39 9
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (34 34
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 7 (:REWRITE RP::BIT-FIX-OPENER))
     (20 20
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (14 14
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 7 (:TYPE-PRESCRIPTION BITP))
     (7 7 (:DEFINITION BITP)))
(RP::RP-EVL-OF-AND-LIST-LEMMA
     (659 659 (:REWRITE DEFAULT-CAR))
     (248 75 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (163 163 (:REWRITE DEFAULT-CDR))
     (114 17 (:DEFINITION RP::IS-SYNP$INLINE))
     (95 75 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (95 75
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (95 75 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (90 70 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (90 70 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (90 70
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (90 70
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (90 70 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (90 70 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (85 65 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (85 65 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (59 59
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (51 10
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (39 39
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 7
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (7 7
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-AND-LIST-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (27 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (27 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-SORT-SUM-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (86 17 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (23 17 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-=-WHEN-MULT-FORMULA-CHECKS
     (353 353 (:REWRITE DEFAULT-CAR))
     (236 38 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (174 19 (:DEFINITION RP::IS-SYNP$INLINE))
     (156 156 (:REWRITE DEFAULT-CDR))
     (50 38 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (48 36 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (48 36 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (46 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL))
     (38 2 (:DEFINITION RP::RP-EQUAL))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (13 13
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (9 9
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6 (:TYPE-PRESCRIPTION RP::RP-EQUAL))
     (6 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL2))
     (6 2
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSE))
     (4 4
        (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
     (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (2 2 (:REWRITE RP::RP-EQUAL-REFLEXIVE)))
(RP::RP-EVL-OF-NFIX-WHEN-MULT-FORMULA-CHECKS
     (376 376 (:REWRITE DEFAULT-CAR))
     (175 32 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (117 15 (:DEFINITION RP::IS-SYNP$INLINE))
     (94 94 (:REWRITE DEFAULT-CDR))
     (46 32 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (46 32 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (46 32 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (46 32 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (46 32 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (46 32 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (46 32
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (45 31
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (45 31
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (45 31
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (44 30
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (44 30
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (44 30
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (44 30
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (44 30
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (44 30 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (44 30
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 10
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (41 27 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (40 26 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (26 26
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (17 17
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-NONNEGATIVE-INTEGER-QUOTIENT-LEMMA
     (519 519 (:REWRITE DEFAULT-CAR))
     (215 67 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (116 116 (:REWRITE DEFAULT-CDR))
     (96 14 (:DEFINITION RP::IS-SYNP$INLINE))
     (83 67
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (83 67
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (83 67
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (83 67
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (83 67 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (83 67 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (83 67
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (79 63 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (79 63 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (79 63 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (79 63 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (79 63
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (77 61
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (75 59
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (75 59
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (75 59
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (75 59 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (75 59
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (71 55 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (71 55 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (69 53 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (54 12
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (52 52
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (36 36
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (27 14
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (24 6 (:REWRITE DEFAULT-<-2))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (18 9 (:REWRITE DEFAULT-+-1))
     (16 9 (:REWRITE DEFAULT-+-2))
     (14 14
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (14 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (13 13
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (12 6 (:REWRITE RP::IFIX-OPENER))
     (12 6 (:REWRITE DEFAULT-<-1))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::RP-EVL-OF-NONNEGATIVE-INTEGER-QUOTIENT-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (27 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (27 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-FLOOR-WHEN-MULT-FORMULA-CHECKS
     (447 447 (:REWRITE DEFAULT-CAR))
     (399 87 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (261 27 (:DEFINITION RP::IS-SYNP$INLINE))
     (244 244 (:REWRITE DEFAULT-CDR))
     (101 87
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (101 87
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (101 87
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (101 87
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (101 87 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (101 87 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (99 85
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (99 85
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (99 85
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (99 85
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (99 85
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (99 85 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (99 85
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (98 84
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (97 83 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (97 83 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (97 83
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (97 83 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (93 79
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (93 79
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (93 79
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (93 79 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (93 79
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (90 76 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (61 13 (:REWRITE DEFAULT-UNARY-/))
     (51 51
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (40 24
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (37 13 (:REWRITE DEFAULT-*-1))
     (36 36
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (33 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (31 10 (:REWRITE DEFAULT-NUMERATOR))
     (26 26
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (24 24
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (20 20
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (20 20
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (20 12 (:REWRITE RATIONALP-*))
     (18 10 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (16 5 (:REWRITE DEFAULT-DENOMINATOR))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (13 13 (:REWRITE DEFAULT-*-2))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (9 5 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (6 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 4 (:REWRITE DEFAULT-+-2))
     (6 4 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1)))
(RP::RP-EVL-OF-C-SPEC-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (88 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (24 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-MOD-WHEN-MULT-FORMULA-CHECKS
     (185 185 (:REWRITE DEFAULT-CAR))
     (126 29 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (76 76 (:REWRITE DEFAULT-CDR))
     (35 29
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (35 29
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (35 29
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (35 29
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (35 29 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (35 29 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (33 27 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (33 27 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (33 27 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (33 27 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (33 27
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (33 27 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (31 25 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (12 4 (:REWRITE DEFAULT-*-2))
     (10 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (10 4 (:REWRITE DEFAULT-*-1))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 2 (:REWRITE DEFAULT-+-1))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 6
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 2 (:REWRITE DEFAULT-+-2)))
(RP::RP-EVL-OF-S-SPEC-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (88 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (24 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-C-S-SPEC-WHEN-MULT-FORMULA-CHECKS
     (172 172 (:REWRITE DEFAULT-CAR))
     (95 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (52 52 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-S-C-SPEC-WHEN-MULT-FORMULA-CHECKS
     (172 172 (:REWRITE DEFAULT-CAR))
     (95 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (52 52 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-ZIP-WHEN-MULT-FORMULA-CHECKS
     (269 269 (:REWRITE DEFAULT-CAR))
     (127 22 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (87 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (32 22 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (32 22 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (32 22 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (32 22 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (32 22 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (32 22 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (32 22
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (29 19 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (24 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (11 11
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-FIX-WHEN-MULT-FORMULA-CHECKS
     (269 269 (:REWRITE DEFAULT-CAR))
     (125 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (87 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (31 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (31 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (31 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (30 20
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (30 20 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 19 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (29 19 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (24 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::RP-EVL-OF-EXPT-LEMMA
     (959 959 (:REWRITE DEFAULT-CAR))
     (354 102 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (219 219
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (177 177 (:REWRITE DEFAULT-CDR))
     (168 26 (:DEFINITION RP::IS-SYNP$INLINE))
     (134 102
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (134 102
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (134 102
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (134 102
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (134 102 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (134 102 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (130 98 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (130 98 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (130 98 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (130 98 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (130 98
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (127 95
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (127 95
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (127 95
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (127 95
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (127 95 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (127 95
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (118 86 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (118 86 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (114 82 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (84 84
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (78 16
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (57 57
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (36 36
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (26 26
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (24 6 (:REWRITE DEFAULT-*-2))
     (21 3 (:REWRITE DEFAULT-UNARY-/))
     (19 11
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (16 16 (:REWRITE DEFAULT-+-2))
     (16 16 (:REWRITE DEFAULT-+-1))
     (15 6 (:REWRITE DEFAULT-*-1))
     (11 11
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (10 10
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (10 10
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4 (:REWRITE ZIP-OPEN))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::RP-EVL-OF-EXPT-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (45 45
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (45 45
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (27 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (27 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-EVENP-WHEN-MULT-FORMULA-CHECKS
     (162 162 (:REWRITE DEFAULT-CAR))
     (87 16 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (46 46 (:REWRITE DEFAULT-CDR))
     (22 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (22 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (22 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (22 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (22 16 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (22 16 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (21 15 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (21 15 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (21 15 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (21 15 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (20 14 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (10 4 (:REWRITE DEFAULT-*-1))
     (9 9
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 4 (:REWRITE DEFAULT-*-2))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-ODDP-WHEN-MULT-FORMULA-CHECKS
     (266 266 (:REWRITE DEFAULT-CAR))
     (120 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (87 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (69 69 (:REWRITE DEFAULT-CDR))
     (28 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (28 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (28 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (27 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (26 16 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (26 16 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-LOGBITP-WHEN-MULT-FORMULA-CHECKS
     (177 177 (:REWRITE DEFAULT-CAR))
     (119 24 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (73 73 (:REWRITE DEFAULT-CDR))
     (30 24 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (30 24
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-LOGBIT$INLINE-WHEN-MULT-FORMULA-CHECKS
     (284 284 (:REWRITE DEFAULT-CAR))
     (179 35 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (123 14 (:DEFINITION RP::IS-SYNP$INLINE))
     (108 108 (:REWRITE DEFAULT-CDR))
     (45 35 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (45 35
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (45 35 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (44 34 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (44 34 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (43 33 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (21 21
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 9
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-BIT-OF-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (132 36 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (42 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-4VEC->UPPER$INLINE-WHEN-MULT-FORMULA-CHECKS
     (393 393 (:REWRITE DEFAULT-CAR))
     (223 40 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (153 18 (:DEFINITION RP::IS-SYNP$INLINE))
     (132 132 (:REWRITE DEFAULT-CDR))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (54 40 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (51 37 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (51 37 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (50 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (48 34 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (48 34 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (33 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (30 30
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (18 18
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (11 11
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (11 11
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-4VEC->LOWER$INLINE-WHEN-MULT-FORMULA-CHECKS
     (391 391 (:REWRITE DEFAULT-CAR))
     (223 40 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (153 18 (:DEFINITION RP::IS-SYNP$INLINE))
     (134 134 (:REWRITE DEFAULT-CDR))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (54 40
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (54 40 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (53 39
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (51 37 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (50 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (48 34 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (48 34 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (33 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (30 30
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (18 18
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 3
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (11 11
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (11 11
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 6
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 3
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-2VEC-P$INLINE-WHEN-MULT-FORMULA-CHECKS
     (276 276 (:REWRITE DEFAULT-CAR))
     (131 26 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (87 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (75 75 (:REWRITE DEFAULT-CDR))
     (36 26 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (36 26
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (36 26 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (35 25 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (35 25 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (35 25
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (35 25 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (35 25 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (35 25 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (35 25 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (22 4
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (11 11
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3 3
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-2VEC->VAL$INLINE-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (88 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (24 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-EQL-WHEN-MULT-FORMULA-CHECKS
     (353 353 (:REWRITE DEFAULT-CAR))
     (236 38 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (174 19 (:DEFINITION RP::IS-SYNP$INLINE))
     (156 156 (:REWRITE DEFAULT-CDR))
     (50 38 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (50 38
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (50 38 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (48 36 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (48 36 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (46 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL))
     (38 2 (:DEFINITION RP::RP-EQUAL))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (13 13
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (9 9
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6 (:TYPE-PRESCRIPTION RP::RP-EQUAL))
     (6 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL2))
     (6 2
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSE))
     (4 4
        (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
     (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (2 2 (:REWRITE RP::RP-EQUAL-REFLEXIVE)))
(RP::RP-EVL-OF-PAIRLIS2-LEMMA
     (484 483 (:REWRITE DEFAULT-CAR))
     (170 46 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (101 100 (:REWRITE DEFAULT-CDR))
     (84 13 (:DEFINITION RP::IS-SYNP$INLINE))
     (62 46 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (62 46
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (62 46 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (58 42 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (58 42
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (56 40
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (56 40 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (54 38 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (54 38 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (52 36 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (40 40
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (36 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (25 25
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-PAIRLIS2-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (27 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (27 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-FMT-TO-COMMENT-WINDOW-WHEN-MULT-FORMULA-CHECKS
     (257 81 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (211 211 (:REWRITE DEFAULT-CAR))
     (153 15 (:DEFINITION RP::IS-SYNP$INLINE))
     (151 151 (:REWRITE DEFAULT-CDR))
     (87 81 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (87 81
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (87 81 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (86 80 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (23 23
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (12 12
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-BREAK$-WHEN-MULT-FORMULA-CHECKS
     (37 7 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (24 2 (:DEFINITION RP::IS-SYNP$INLINE))
     (20 20 (:REWRITE DEFAULT-CDR))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (9 5 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (7 7
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (7 7 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (6 6 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (2 2
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-CHECK-DCL-GUARDIAN-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 19 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (25 19 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-LIFIX$INLINE-WHEN-MULT-FORMULA-CHECKS
     (162 162 (:REWRITE DEFAULT-CAR))
     (81 13 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (46 46 (:REWRITE DEFAULT-CDR))
     (19 13 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (18 12
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (17 11 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (17 11 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-4VEC-WHEN-MULT-FORMULA-CHECKS
     (329 319 (:REWRITE DEFAULT-CAR))
     (226 53 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (149 143 (:REWRITE DEFAULT-CDR))
     (147 16 (:DEFINITION RP::IS-SYNP$INLINE))
     (63 53 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (63 53
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (63 53 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (60 50
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (60 50 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (56 46 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (26 26
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (11 11
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (11 11
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-2VEC$INLINE-WHEN-MULT-FORMULA-CHECKS
     (177 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (172 172 (:REWRITE DEFAULT-CAR))
     (93 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (52 52 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (28 22
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (22 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 2
        (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 4 (:REWRITE RP::IFIX-OPENER))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:DEFINITION BITP)))
(RP::RP-EVL-OF-ASH-WHEN-MULT-FORMULA-CHECKS
     (177 177 (:REWRITE DEFAULT-CAR))
     (123 26 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (73 73 (:REWRITE DEFAULT-CDR))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (31 25
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 2 (:REWRITE DEFAULT-*-2))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (4 2 (:REWRITE DEFAULT-*-1))
     (2 2
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (2 2 (:TYPE-PRESCRIPTION IFIX))
     (2 2
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-4VEC-SHIFT-CORE-WHEN-MULT-FORMULA-CHECKS
     (267 251 (:REWRITE DEFAULT-CAR))
     (228 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (194 88 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (118 111 (:REWRITE DEFAULT-CDR))
     (94 88 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (92 86 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (92 86
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (92 86 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (92 86 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (91 85 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (91 85 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (28 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (25 25
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (17 5
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (16 16
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (9 9
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:DEFINITION BITP)))
(RP::RP-EVL-OF-4VEC-RSH-WHEN-MULT-FORMULA-CHECKS
     (307 307 (:REWRITE DEFAULT-CAR))
     (250 52 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (171 18 (:DEFINITION RP::IS-SYNP$INLINE))
     (159 159 (:REWRITE DEFAULT-CDR))
     (62 52 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (62 52 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (62 52 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (62 52 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (62 52 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (62 52 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (62 52
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (62 52 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (61 51
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (61 51
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (61 51
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (61 51 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (61 51
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (60 50 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (60 50 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 27
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 4
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (13 13
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (12 12
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2
        (:TYPE-PRESCRIPTION SV::2VEC->VAL$INLINE))
     (2 2
        (:REWRITE SV::4VEC-SHIFT-CORE-OF-IFIX-AMT-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::4VEC-SHIFT-CORE-OF-4VEC-FIX-SRC-NORMALIZE-CONST)))
(RP::RP-EVL-OF-THE-CHECK-WHEN-MULT-FORMULA-CHECKS
     (188 188 (:REWRITE DEFAULT-CAR))
     (157 36 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (99 99 (:REWRITE DEFAULT-CDR))
     (42 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (41 35 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-BINARY-LOGAND-LEMMA
     (1230 1221 (:REWRITE DEFAULT-CAR))
     (497 142 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (261 255 (:REWRITE DEFAULT-CDR))
     (240 35 (:DEFINITION RP::IS-SYNP$INLINE))
     (182 142
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (182 142
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (182 142
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (182 142
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (182 142 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (182 142 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (180 140
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (180 140 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (164 124 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (164 124
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (115 115
          (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (105 20
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (74 74
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (50 50
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (35 35
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (16 10 (:REWRITE DEFAULT-+-2))
     (16 10 (:REWRITE DEFAULT-+-1))
     (15 15 (:TYPE-PRESCRIPTION FLOOR))
     (15 15
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (15 15
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (15 7 (:REWRITE DEFAULT-*-2))
     (12 2 (:REWRITE O-INFP->NEQ-0))
     (11 11 (:REWRITE ZIP-OPEN))
     (7 7 (:REWRITE DEFAULT-*-1))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::RP-EVL-OF-BINARY-LOGAND-WHEN-MULT-FORMULA-CHECKS
     (169 169 (:REWRITE DEFAULT-CAR))
     (114 21 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (70 70 (:REWRITE DEFAULT-CDR))
     (27 21 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (27 21
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (27 21
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (27 21 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 2
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-EXPT2$INLINE-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (90 19 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (25 19 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (9 9
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-IMOD$INLINE-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (134 37 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (43 37 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 4 (:REWRITE RP::IFIX-OPENER))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-LOGHEAD$INLINE-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (134 37 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (43 37 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-LOGAPP-WHEN-MULT-FORMULA-CHECKS
     (247 243 (:REWRITE DEFAULT-CAR))
     (217 90 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (128 127 (:REWRITE DEFAULT-CDR))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (96 90
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (96 90
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (96 90
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (96 90
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (96 90 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (96 90 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (94 88
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (94 88 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (93 87 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (93 87 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (93 87
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (93 87 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (93 87 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (93 87 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (93 87 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (22 22
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (11 11
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 4 (:REWRITE DEFAULT-*-2))
     (10 4 (:REWRITE DEFAULT-*-1))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (8 2 (:REWRITE DEFAULT-+-2))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 3 (:REWRITE RP::IFIX-OPENER))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE SVL::LOGHEAD-NON-POS-SIZE))
     (4 2 (:REWRITE DEFAULT-+-1)))
(RP::RP-EVL-OF-4VEC-CONCAT-WHEN-MULT-FORMULA-CHECKS
     (1631 314 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (1185 104 (:DEFINITION RP::IS-SYNP$INLINE))
     (1126 1116 (:REWRITE DEFAULT-CDR))
     (757 716 (:REWRITE DEFAULT-CAR))
     (328 314 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (328 314 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (328 314 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (328 314 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (328 314 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (328 314
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (327 313
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (327 313
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (327 313
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (327 313 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (327 313 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (327 313 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (327 313 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (327 313
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (325 311 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (325 311
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (325 311 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (325 311 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (321 307
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (132 132
          (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (97 97
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (97 97
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (45 11
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (38 26
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (27 27
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (19 19
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (4 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE DEFAULT-<-2)))
(RP::RP-EVL-OF-4VEC-ZERO-EXT-WHEN-MULT-FORMULA-CHECKS
     (638 119 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (512 501 (:REWRITE DEFAULT-CAR))
     (453 43 (:DEFINITION RP::IS-SYNP$INLINE))
     (432 427 (:REWRITE DEFAULT-CDR))
     (133 119 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (133 119 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (133 119 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (133 119 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (133 119 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (133 119
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (132 118
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (132 118
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (132 118
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (132 118 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (132 118 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (132 118 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (132 118 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (132 118
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (130 116 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (130 116
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (130 116 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (130 116 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (126 112
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (66 66
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (45 11
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (36 36
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (36 36
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (25 25
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (19 19
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (13 7
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (10 4 (:REWRITE SVL::LOGHEAD-NON-POS-SIZE))
     (6 6
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (6 5 (:REWRITE DEFAULT-<-1))
     (5 5 (:REWRITE DEFAULT-<-2)))
(RP::RP-EVL-OF-4VEC-PART-SELECT-WHEN-MULT-FORMULA-CHECKS
     (1054 206 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (768 767 (:REWRITE DEFAULT-CAR))
     (753 71 (:DEFINITION RP::IS-SYNP$INLINE))
     (699 698 (:REWRITE DEFAULT-CDR))
     (228 206 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (228 206 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (228 206 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (228 206 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (228 206 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (228 206
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (226 204
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (225 203
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (225 203
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (225 203
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (225 203 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (225 203
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (219 197
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (95 95
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (63 15
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (60 60
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (60 60
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (31 31
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (27 27
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (21 21
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (11 11
         (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (9 7 (:REWRITE DEFAULT-<-1))
     (7 7 (:REWRITE DEFAULT-<-2))
     (4 4
        (:REWRITE SV::4VEC-ZERO-EXT-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (4 4
        (:REWRITE SV::4VEC-ZERO-EXT-OF-4VEC-FIX-N-NORMALIZE-CONST))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:REWRITE SV::4VEC-RSH-OF-4VEC-FIX-SRC-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::4VEC-RSH-OF-2VECX-FIX-AMT-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::4VEC-CONCAT-OF-4VEC-FIX-LOW-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::4VEC-CONCAT-OF-4VEC-FIX-HIGH-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::4VEC-CONCAT-OF-2VECNATX-FIX-WIDTH-NORMALIZE-CONST)))
(RP::RP-EVL-OF-BITS-WHEN-MULT-FORMULA-CHECKS
     (218 218 (:REWRITE DEFAULT-CAR))
     (192 69 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (115 115 (:REWRITE DEFAULT-CDR))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (75 69 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-LOGNOT-WHEN-MULT-FORMULA-CHECKS
     (162 162 (:REWRITE DEFAULT-CAR))
     (85 15 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (46 46 (:REWRITE DEFAULT-CDR))
     (21 15
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (21 15 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (21 15 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (21 15
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (20 14 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (20 14 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (20 14 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (20 14 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (20 14
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (20 14 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (19 13 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (19 13
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (18 12 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 4 (:REWRITE DEFAULT-+-2))
     (6 4 (:REWRITE DEFAULT-+-1))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-LOGANDC2-WHEN-MULT-FORMULA-CHECKS
     (177 177 (:REWRITE DEFAULT-CAR))
     (117 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (73 73 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (28 22 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-3VEC-P-WHEN-MULT-FORMULA-CHECKS
     (197 192 (:REWRITE DEFAULT-CAR))
     (108 33 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (65 62 (:REWRITE DEFAULT-CDR))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (39 33 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (39 33
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (39 33 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (38 32 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (38 32 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (38 32
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (38 32 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (38 32 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (38 32 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (38 32 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (11 11
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (11 5
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION SV::INTEGERP-OF-4VEC->LOWER))
     (4 4
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3 3
        (:TYPE-PRESCRIPTION SV::INTEGERP-OF-4VEC->UPPER))
     (2 2
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-BINARY-LOGIOR-WHEN-MULT-FORMULA-CHECKS
     (177 177 (:REWRITE DEFAULT-CAR))
     (117 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (73 73 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (28 22 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-3VEC-FIX-WHEN-MULT-FORMULA-CHECKS
     (208 200 (:REWRITE DEFAULT-CAR))
     (177 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (114 39 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (70 65 (:REWRITE DEFAULT-CDR))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (45 39 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (45 39
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (45 39 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (22 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (17 5
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (13 13
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 8
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (5 1 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (2 2 (:DEFINITION BITP))
     (2 1 (:REWRITE SVL::REMOVE-3VEC-FIX))
     (2 1
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (1 1
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-3VEC-BITAND-WHEN-MULT-FORMULA-CHECKS
     (324 295 (:REWRITE DEFAULT-CAR))
     (238 133 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (228 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (143 133 (:REWRITE DEFAULT-CDR))
     (139 133 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (138 132
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (138 132
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (39 21
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (22 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (14 14
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (12 12
         (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (6 6
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:DEFINITION BITP))
     (1 1
        (:REWRITE SV::3VEC-BITAND-OF-4VEC-FIX-Y-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::3VEC-BITAND-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-4VEC-BITAND-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (132 36 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (42 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (20 4 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 4 (:REWRITE SVL::REMOVE-3VEC-FIX))
     (8 4
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-BITAND-OF-4VEC-FIX-Y-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-BITAND-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-3VEC-BITOR-WHEN-MULT-FORMULA-CHECKS
     (324 295 (:REWRITE DEFAULT-CAR))
     (238 133 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (228 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (143 133 (:REWRITE DEFAULT-CDR))
     (139 133 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (139 133
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (139 133 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (138 132
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (138 132
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (138 132 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (39 21
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (22 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (14 14
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (12 12
         (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (6 6
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:DEFINITION BITP))
     (1 1
        (:REWRITE SV::3VEC-BITOR-OF-4VEC-FIX-Y-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::3VEC-BITOR-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-4VEC-BITOR-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (132 36 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (42 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (20 4 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 4 (:REWRITE SVL::REMOVE-3VEC-FIX))
     (8 4
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-BITOR-OF-4VEC-FIX-Y-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-BITOR-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-4VEC-FIX$INLINE-WHEN-MULT-FORMULA-CHECKS
     (398 398 (:REWRITE DEFAULT-CAR))
     (240 43 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (165 19 (:DEFINITION RP::IS-SYNP$INLINE))
     (146 146 (:REWRITE DEFAULT-CDR))
     (57 43
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (57 43
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (57 43
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (57 43
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (57 43 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (56 42 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (56 42 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (56 42 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (56 42 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (56 42
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (55 41 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (55 41
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (55 41 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (53 39 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (52 38
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (52 38 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (50 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (33 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (32 32
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (19 19
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (12 12
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (10 2
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (8 4 (:REWRITE RP::IFIX-OPENER))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (4 2
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (2 2 (:REWRITE SVL::BITP-IMPLIES-4VECP)))
(RP::RP-EVL-OF-3VEC-?-WHEN-MULT-FORMULA-CHECKS
     (1209 287 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (834 817 (:REWRITE DEFAULT-CDR))
     (825 74 (:DEFINITION RP::IS-SYNP$INLINE))
     (740 693 (:REWRITE DEFAULT-CAR))
     (301 287 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (298 284
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (97 97
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (67 67
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (67 67
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (60 4 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (51 27
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (30 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (22 22
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (20 4
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (16 16
         (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (12 4 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (8 8
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (8 8
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (8 4
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 4
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION BITP))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:DEFINITION BITP)))
(RP::RP-EVL-OF-4VEC-?-WHEN-MULT-FORMULA-CHECKS
     (218 218 (:REWRITE DEFAULT-CAR))
     (192 69 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (115 115 (:REWRITE DEFAULT-CDR))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (75 69 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 2 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE SVL::REMOVE-3VEC-FIX))
     (4 2
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (2 2
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-?-OF-4VEC-FIX-THEN-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-?-OF-4VEC-FIX-TEST-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-?-OF-4VEC-FIX-ELSE-NORMALIZE-CONST)))
(RP::RP-EVL-OF-LOGORC1-WHEN-MULT-FORMULA-CHECKS
     (177 177 (:REWRITE DEFAULT-CAR))
     (117 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (73 73 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (28 22 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-BINARY-LOGEQV-WHEN-MULT-FORMULA-CHECKS
     (185 185 (:REWRITE DEFAULT-CAR))
     (120 26 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (76 76 (:REWRITE DEFAULT-CDR))
     (32 26 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (32 26
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (32 26 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (31 25 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (31 25 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-BINARY-LOGXOR-WHEN-MULT-FORMULA-CHECKS
     (177 177 (:REWRITE DEFAULT-CAR))
     (117 23 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (73 73 (:REWRITE DEFAULT-CDR))
     (29 23 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (29 23
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (29 23 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (28 22 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (28 22 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (5 5
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::RP-EVL-OF-3VEC-?*-WHEN-MULT-FORMULA-CHECKS
     (1209 287 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (834 817 (:REWRITE DEFAULT-CDR))
     (825 74 (:DEFINITION RP::IS-SYNP$INLINE))
     (740 693 (:REWRITE DEFAULT-CAR))
     (301 287 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (301 287
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (301 287 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (298 284
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (97 97
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (67 67
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (67 67
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (60 4 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (51 27
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (30 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (22 22
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (20 4
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (16 16
         (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (12 4 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (8 8
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (8 8
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (8 4
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 4
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION BITP))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:DEFINITION BITP)))
(RP::RP-EVL-OF-4VEC-?*-WHEN-MULT-FORMULA-CHECKS
     (218 218 (:REWRITE DEFAULT-CAR))
     (192 69 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (115 115 (:REWRITE DEFAULT-CDR))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (75 69 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 2 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE SVL::REMOVE-3VEC-FIX))
     (4 2
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (2 2
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-?*-OF-4VEC-FIX-THEN-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-?*-OF-4VEC-FIX-TEST-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-?*-OF-4VEC-FIX-ELSE-NORMALIZE-CONST)))
(RP::RP-EVL-OF-4VEC-BITXOR-WHEN-MULT-FORMULA-CHECKS
     (417 362 (:REWRITE DEFAULT-CAR))
     (312 205 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (228 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (211 205 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (211 205
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (211 205 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (210 204 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (210 204 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (210 204
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (210 204 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (210 204 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (210 204
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (210 204 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (184 164 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (65 47
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (26 26
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (22 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (15 15
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (12 12
         (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (6 6
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:DEFINITION BITP))
     (1 1
        (:REWRITE SV::4VEC-BITXOR-OF-3VEC-FIX-Y-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::4VEC-BITXOR-OF-3VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-3VEC-BITNOT-WHEN-MULT-FORMULA-CHECKS
     (197 192 (:REWRITE DEFAULT-CAR))
     (177 3
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (109 35 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (65 62 (:REWRITE DEFAULT-CDR))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (41 35 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (41 35
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (41 35 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (40 34 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (40 34 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (40 34
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (40 34 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (40 34 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (40 34 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (40 34 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (22 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (19 7
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (12 12
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 8
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 3 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (6 6
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (5 3
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:DEFINITION BITP))
     (1 1
        (:REWRITE SV::3VEC-BITNOT-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-4VEC-BITNOT-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (86 17 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (23 17 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (10 2 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE SVL::REMOVE-3VEC-FIX))
     (4 2
        (:REWRITE SVL::INTEGERP-IMPLIES-3VEC-P))
     (2 2
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::3VEC-BITNOT-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-4VEC-BITNOT$-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (134 37 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (43 37 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (2 2
        (:REWRITE SV::4VEC-BITNOT-OF-3VEC-FIX-X-NORMALIZE-CONST)))
(RP::RP-EVL-OF-ADDER-B+-WHEN-MULT-FORMULA-CHECKS
     (190 190 (:REWRITE DEFAULT-CAR))
     (134 37 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 81 (:REWRITE DEFAULT-CDR))
     (81 9 (:DEFINITION RP::IS-SYNP$INLINE))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (43 37 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (43 37
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 36
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 4 (:REWRITE RP::IFIX-OPENER))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (6 6
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE DEFAULT-+-2))
     (4 2 (:REWRITE DEFAULT-+-1)))
(RP::RP-EVL-OF-S-OF-C-TRIG-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (86 17 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (23 17 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (23 17
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (23 17 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4 (:TYPE-PRESCRIPTION RP::S-OF-C-TRIG))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-BINARY-?-WHEN-MULT-FORMULA-CHECKS
     (350 86 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (334 334 (:REWRITE DEFAULT-CAR))
     (231 23 (:DEFINITION RP::IS-SYNP$INLINE))
     (222 222 (:REWRITE DEFAULT-CDR))
     (96 86 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (96 86
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (96 86 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (95 85 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (95 85 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (33 33
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (24 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (21 7 (:REWRITE RP::BIT-FIX-OPENER))
     (18 18
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (18 18
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (12 12
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 7 (:TYPE-PRESCRIPTION BITP))
     (7 7 (:DEFINITION BITP)))
(RP::RP-EVL-OF-BINARY-XOR-WHEN-MULT-FORMULA-CHECKS
     (297 297 (:REWRITE DEFAULT-CAR))
     (196 49 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (123 14 (:DEFINITION RP::IS-SYNP$INLINE))
     (116 116 (:REWRITE DEFAULT-CDR))
     (59 49 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (59 49
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (59 49 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (58 48 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (58 48 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (24 5
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (18 6 (:REWRITE RP::BIT-FIX-OPENER))
     (13 13
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 9
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6 (:TYPE-PRESCRIPTION BITP))
     (6 6 (:DEFINITION BITP)))
(RP::RP-EVL-OF-BINARY-OR-WHEN-MULT-FORMULA-CHECKS
     (406 406 (:REWRITE DEFAULT-CAR))
     (286 63 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (189 21 (:DEFINITION RP::IS-SYNP$INLINE))
     (171 171 (:REWRITE DEFAULT-CDR))
     (77 63 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (77 63
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (77 63 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (75 61 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (75 61 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (39 9
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (34 34
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (21 7 (:REWRITE RP::BIT-FIX-OPENER))
     (20 20
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (17 17
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (14 14
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (7 7 (:TYPE-PRESCRIPTION BITP))
     (7 7 (:DEFINITION BITP))
     (6 3 (:REWRITE O-INFP->NEQ-0)))
(RP::RP-EVL-OF-BINARY-NOT-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (92 20 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (25 19
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (25 19 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 10
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 2 (:REWRITE RP::BIT-FIX-OPENER))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2 (:DEFINITION BITP)))
(RP::RP-EVL-OF-C-RES-WHEN-MULT-FORMULA-CHECKS
     (320 40
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (218 218 (:REWRITE DEFAULT-CAR))
     (192 69 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (115 115 (:REWRITE DEFAULT-CDR))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (86 4
         (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (75 69 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (75 69
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (75 69 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (18 18
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-C-WHEN-MULT-FORMULA-CHECKS
     (364 44
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (250 99 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (238 238 (:REWRITE DEFAULT-CAR))
     (145 145 (:REWRITE DEFAULT-CDR))
     (129 13 (:DEFINITION RP::IS-SYNP$INLINE))
     (105 99 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (105 99
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (105 99 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (86 4
         (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (22 22
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (10 10
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (10 10
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-EVL-OF-M2-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (88 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (24 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-F2-WHEN-MULT-FORMULA-CHECKS
     (168 168 (:REWRITE DEFAULT-CAR))
     (88 18 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (50 50 (:REWRITE DEFAULT-CDR))
     (24 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (24 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (24 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (13 13
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EVL-OF-TIMES2-WHEN-MULT-FORMULA-CHECKS
     (172 172 (:REWRITE DEFAULT-CAR))
     (89 20 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (57 7 (:DEFINITION RP::IS-SYNP$INLINE))
     (52 52 (:REWRITE DEFAULT-CDR))
     (26 20 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (26 20
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (26 20 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (20 4
         (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (2 2 (:REWRITE RP::SUM-COMM-1)))
(RP::RP-EVL-OF-S-WHEN-MULT-FORMULA-CHECKS
     (206 206 (:REWRITE DEFAULT-CAR))
     (178 54 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (109 109 (:REWRITE DEFAULT-CDR))
     (105 11 (:DEFINITION RP::IS-SYNP$INLINE))
     (88 8
         (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (60 54 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (60 54
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (60 54 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (19 19
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (15 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
