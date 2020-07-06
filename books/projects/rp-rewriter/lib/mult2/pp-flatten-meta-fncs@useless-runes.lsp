(RP::PP-LIST-ORDER-AUX
     (739 1 (:REWRITE O<=-O-FINP-DEF))
     (688 2 (:LINEAR ACL2-COUNT-OF-SUM))
     (307 102 (:REWRITE DEFAULT-+-2))
     (184 102 (:REWRITE DEFAULT-+-1))
     (176 176
          (:TYPE-PRESCRIPTION ACL2-COUNT-OF-CONSP-POSITIVE))
     (165 11 (:DEFINITION LENGTH))
     (121 11 (:DEFINITION LEN))
     (110 22 (:REWRITE COMMUTATIVITY-OF-+))
     (88 22 (:DEFINITION INTEGER-ABS))
     (64 31 (:REWRITE DEFAULT-CDR))
     (33 33
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (33 22 (:REWRITE STR::CONSP-OF-EXPLODE))
     (28 28 (:REWRITE FOLD-CONSTS-IN-+))
     (27 23 (:REWRITE DEFAULT-<-2))
     (25 23 (:REWRITE DEFAULT-<-1))
     (24 6 (:REWRITE O-P-O-INFP-CAR))
     (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
     (22 11
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (21 21 (:REWRITE DEFAULT-CAR))
     (11 11 (:TYPE-PRESCRIPTION LEN))
     (11 11
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (11 11 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (11 11 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (11 11
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (11 11
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (11 11
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (11 11 (:REWRITE DEFAULT-REALPART))
     (11 11 (:REWRITE DEFAULT-NUMERATOR))
     (11 11 (:REWRITE DEFAULT-IMAGPART))
     (11 11 (:REWRITE DEFAULT-DENOMINATOR))
     (7 1 (:REWRITE AC-<))
     (6 6 (:REWRITE O-P-DEF-O-FINP-1))
     (5 1
        (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
     (4 4
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (3 3
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (3 1 (:REWRITE O-INFP-O-FINP-O<=))
     (2 2
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (2 2
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (1 1
        (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::BOOLEANP-OF-PP-LIST-ORDER-AUX.EQUALS
     (22 22 (:REWRITE DEFAULT-CAR))
     (12 1 (:REWRITE <<-IMPLIES-LEXORDER))
     (8 2 (:REWRITE <<-TRICHOTOMY))
     (6 6 (:TYPE-PRESCRIPTION <<))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE <<-TRANSITIVE))
     (2 1 (:REWRITE <<-ASYMMETRIC))
     (1 1 (:REWRITE LEXORDER-TRANSITIVE)))
(RP::PP-LIST-ORDER)
(RP::BOOLEANP-OF-PP-LIST-ORDER.EQUALS
     (10 2 (:DEFINITION LEN))
     (10 1 (:REWRITE LEN-WHEN-PREFIXP))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:TYPE-PRESCRIPTION PREFIXP))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 1 (:REWRITE DEFAULT-<-2))
     (2 1 (:REWRITE DEFAULT-<-1))
     (1 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (1 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (1 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (1 1
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (1 1
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(RP::PP-LISTS-P)
(RP::PP-HAS-BITP-RP (14312 48 (:LINEAR ACL2-COUNT-OF-SUM))
                    (11343 43 (:DEFINITION APPLY$-BADGEP))
                    (7456 3 (:REWRITE O<=-O-FINP-DEF))
                    (7299 74
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                    (5136 28 (:DEFINITION SUBSETP-EQUAL))
                    (4772 392 (:DEFINITION MEMBER-EQUAL))
                    (4241 48
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                    (3492 56
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                    (2976 196
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                    (2536 28 (:DEFINITION TRUE-LISTP))
                    (2225 763 (:REWRITE DEFAULT-+-2))
                    (1864 56 (:DEFINITION RP::RP-TERM-LISTP))
                    (1416 116
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                    (1347 763 (:REWRITE DEFAULT-+-1))
                    (1290 86 (:DEFINITION LENGTH))
                    (1195 1195
                          (:TYPE-PRESCRIPTION ACL2-COUNT-OF-CONSP-POSITIVE))
                    (1192 12 (:DEFINITION RP::RP-TERMP))
                    (1142 114 (:DEFINITION LEN))
                    (924 924 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                    (868 868 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                    (860 172 (:REWRITE COMMUTATIVITY-OF-+))
                    (828 4 (:DEFINITION RP::FALIST-CONSISTENT))
                    (690 56 (:DEFINITION NATP))
                    (688 172 (:DEFINITION INTEGER-ABS))
                    (644 4
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                    (588 588
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                    (448 192 (:REWRITE RP::IS-IF-RP-TERMP))
                    (420 420 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                    (392 392
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                    (384 86 (:REWRITE O-P-O-INFP-CAR))
                    (360 116
                         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                    (288 288
                         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                    (282 282 (:TYPE-PRESCRIPTION LEN))
                    (258 258
                         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                    (258 172 (:REWRITE STR::CONSP-OF-EXPLODE))
                    (249 233 (:REWRITE DEFAULT-<-2))
                    (243 233 (:REWRITE DEFAULT-<-1))
                    (224 112
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                    (210 60
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                    (192 192
                         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                    (192 96
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                    (172 172 (:REWRITE DEFAULT-UNARY-MINUS))
                    (172 86
                         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                    (172 43 (:DEFINITION WEAK-APPLY$-BADGE-P))
                    (168 28 (:DEFINITION ALL-NILS))
                    (160 64 (:REWRITE RP::RP-TERMP-CADDDR))
                    (144 64 (:REWRITE RP::RP-TERMP-CADR))
                    (144 64 (:REWRITE RP::RP-TERMP-CADDR))
                    (144 64 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                    (142 142
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (140 140 (:TYPE-PRESCRIPTION ALL-NILS))
                    (121 29 (:DEFINITION QUOTEP))
                    (116 116 (:TYPE-PRESCRIPTION QUOTEP))
                    (114 114
                         (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                    (112 112 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                    (112 112 (:LINEAR LEN-WHEN-PREFIXP))
                    (111 111
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                    (89 29
                        (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
                    (86 86
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (86 86 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                    (86 86
                        (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                    (86 86
                        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                    (86 86 (:REWRITE DEFAULT-REALPART))
                    (86 86 (:REWRITE DEFAULT-NUMERATOR))
                    (86 86 (:REWRITE DEFAULT-IMAGPART))
                    (86 86 (:REWRITE DEFAULT-DENOMINATOR))
                    (82 6
                        (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
                    (78 78
                        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                    (64 64 (:TYPE-PRESCRIPTION O-FINP))
                    (58 58
                        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                    (56 56
                        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                    (41 41
                        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                    (36 36
                        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                    (32 32 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                    (28 28
                        (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                    (21 3 (:REWRITE AC-<))
                    (20 4
                        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                    (16 2 (:REWRITE O-FIRST-EXPT-<))
                    (12 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                    (9 3 (:REWRITE O-INFP-O-FINP-O<=))
                    (6 2 (:REWRITE O-FIRST-COEFF-<))
                    (4 4
                       (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                    (3 3
                       (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::PP-TERM-P (18079 205 (:DEFINITION RP::EX-FROM-RP))
               (15726 3756 (:REWRITE RP::MEASURE-LEMMA1))
               (15360 400 (:REWRITE RP::NOT-INCLUDE-RP))
               (14702 226 (:DEFINITION RP::INCLUDE-FNC))
               (13534 1392 (:REWRITE RP::MEASURE-LEMMA1-2))
               (10697 141 (:DEFINITION APPLY$-BADGEP))
               (10121 165
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
               (4961 3561 (:REWRITE DEFAULT-CDR))
               (4782 18
                     (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
               (4207 9 (:DEFINITION TRUE-LISTP))
               (3528 45
                     (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
               (3456 27 (:DEFINITION RP::RP-TERMP))
               (3080 1821 (:REWRITE DEFAULT-CAR))
               (2799 9 (:DEFINITION SUBSETP-EQUAL))
               (2646 126 (:DEFINITION MEMBER-EQUAL))
               (2502 9 (:DEFINITION RP::FALIST-CONSISTENT))
               (1962 9
                     (:DEFINITION RP::FALIST-CONSISTENT-AUX))
               (1692 63
                     (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
               (1285 271 (:DEFINITION QUOTEP))
               (1092 1092
                     (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
               (1076 18 (:DEFINITION RP::RP-TERM-LISTP))
               (1052 120
                     (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
               (959 959
                    (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
               (939 66 (:DEFINITION NATP))
               (756 141 (:DEFINITION WEAK-APPLY$-BADGE-P))
               (700 20 (:REWRITE RP::EX-FROM-RP-X2))
               (585 585 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
               (453 45
                    (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
               (434 122 (:REWRITE O-P-O-INFP-CAR))
               (412 412
                    (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
               (360 108 (:REWRITE RP::IS-IF-RP-TERMP))
               (279 279 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
               (222 99
                    (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
               (206 81
                    (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
               (189 189
                    (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
               (144 36 (:REWRITE RP::RP-TERMP-CADDDR))
               (126 126
                    (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
               (120 40 (:REWRITE RP::CONS-COUNT-ATOM))
               (108 108
                    (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
               (108 108
                    (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
               (108 36 (:REWRITE RP::RP-TERMP-CADR))
               (108 36 (:REWRITE RP::RP-TERMP-CADDR))
               (108 36 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
               (107 9 (:DEFINITION LEN))
               (104 104 (:REWRITE O-P-DEF-O-FINP-1))
               (104 36
                    (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
               (104 4 (:REWRITE O<=-O-FINP-DEF))
               (99 99
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (90 9 (:DEFINITION ALL-NILS))
               (81 81
                   (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
               (72 72 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
               (63 63 (:TYPE-PRESCRIPTION LEN))
               (63 9
                   (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
               (51 51
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
               (45 45 (:TYPE-PRESCRIPTION QUOTEP))
               (45 45 (:TYPE-PRESCRIPTION ALL-NILS))
               (43 43
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
               (40 8 (:REWRITE RP::MEASURE-LEMMA7-2))
               (37 35 (:REWRITE DEFAULT-<-2))
               (37 35 (:REWRITE DEFAULT-<-1))
               (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
               (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
               (35 35
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
               (18 18
                   (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
               (18 18 (:LINEAR LEN-WHEN-PREFIXP))
               (18 9 (:REWRITE DEFAULT-+-2))
               (12 4 (:REWRITE AC-<))
               (9 9
                  (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
               (9 9 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
               (9 9 (:REWRITE DEFAULT-+-1))
               (8 4 (:REWRITE O-INFP-O-FINP-O<=))
               (4 4
                  (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::CUT-LIST-BY-HALF)
(RP::TRUE-LISTP-OF-CUT-LIST-BY-HALF.FIRST
     (4198 21
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (4065 7 (:DEFINITION TRUE-LISTP))
     (2196 14 (:DEFINITION RP::RP-TERM-LISTP))
     (2007 28
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1981 28
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1944 28 (:DEFINITION QUOTEP))
     (1904 7 (:DEFINITION RP::RP-TERMP))
     (1867 14
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1853 7 (:DEFINITION APPLY$-BADGEP))
     (1449 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (1377 1377 (:REWRITE DEFAULT-CDR))
     (1293 7 (:DEFINITION SUBSETP-EQUAL))
     (1202 98 (:DEFINITION MEMBER-EQUAL))
     (1127 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (750 49
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (687 687 (:REWRITE DEFAULT-CAR))
     (294 84 (:REWRITE O-P-O-INFP-CAR))
     (259 259 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (217 217 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (147 147
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (140 140 (:TYPE-PRESCRIPTION O-P))
     (133 14 (:DEFINITION NATP))
     (98 98
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (91 91
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (84 35 (:REWRITE RP::IS-IF-RP-TERMP))
     (70 70 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (70 70 (:REWRITE O-P-DEF-O-FINP-1))
     (63 63
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (63 63
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (56 56 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (56 21 (:REWRITE RP::RP-TERMP-CADR))
     (49 49 (:TYPE-PRESCRIPTION LEN))
     (49 7 (:DEFINITION LEN))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (42 7 (:DEFINITION ALL-NILS))
     (35 35 (:TYPE-PRESCRIPTION ALL-NILS))
     (35 7
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (33 26 (:REWRITE DEFAULT-+-2))
     (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (28 28 (:TYPE-PRESCRIPTION QUOTEP))
     (28 14 (:REWRITE RP::RP-TERMP-CADDR))
     (28 14 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (28 7 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (26 26 (:REWRITE DEFAULT-+-1))
     (21 21
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (21 21
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14 (:LINEAR LEN-WHEN-PREFIXP))
     (14 7
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (14 7
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (7 7
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE ZP-OPEN)))
(RP::TRUE-LISTP-OF-CUT-LIST-BY-HALF.SECOND
     (19527 91
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (10470 108
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (10225 108 (:DEFINITION QUOTEP))
     (10157 50 (:DEFINITION RP::RP-TERM-LISTP))
     (9856 38 (:DEFINITION APPLY$-BADGEP))
     (8894 74
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (8239 108
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (7952 29 (:DEFINITION RP::RP-TERMP))
     (6819 37 (:DEFINITION SUBSETP-EQUAL))
     (6437 6437 (:REWRITE DEFAULT-CDR))
     (6338 518 (:DEFINITION MEMBER-EQUAL))
     (6003 29 (:DEFINITION RP::FALIST-CONSISTENT))
     (4669 29
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3954 259
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3021 3021 (:REWRITE DEFAULT-CAR))
     (1218 348 (:REWRITE O-P-O-INFP-CAR))
     (1147 1147 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1118 37
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (777 777
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (728 74 (:DEFINITION NATP))
     (580 580 (:TYPE-PRESCRIPTION O-P))
     (518 518
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (396 157 (:REWRITE RP::IS-IF-RP-TERMP))
     (388 388 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (349 349
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (290 290 (:REWRITE O-P-DEF-O-FINP-1))
     (261 261
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (259 259 (:TYPE-PRESCRIPTION LEN))
     (259 37 (:DEFINITION LEN))
     (257 257
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (232 87 (:REWRITE RP::RP-TERMP-CADR))
     (230 115
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (224 224 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (222 111
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (222 37 (:DEFINITION ALL-NILS))
     (185 185 (:TYPE-PRESCRIPTION ALL-NILS))
     (170 133 (:REWRITE DEFAULT-+-2))
     (152 38 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (148 148 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (145 29
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (133 133 (:REWRITE DEFAULT-+-1))
     (132 62 (:REWRITE RP::RP-TERMP-CADDR))
     (132 62 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (111 111
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (108 108 (:TYPE-PRESCRIPTION QUOTEP))
     (107 49
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (91 91
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (82 82 (:LINEAR LEN-WHEN-PREFIXP))
     (58 58
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (37 37 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (37 37 (:REWRITE DEFAULT-<-2))
     (37 37 (:REWRITE DEFAULT-<-1))
     (32 8 (:REWRITE RP::RP-TERMP-CADDDR))
     (29 29
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (11 11 (:REWRITE ZP-OPEN)))
(RP::CUT-LIST-BY-HALF-RETURNS-PP-LISTS
     (16150 63
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (14512 21 (:DEFINITION TRUE-LISTP))
     (8716 42 (:DEFINITION RP::RP-TERM-LISTP))
     (8275 147
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (7624 147 (:DEFINITION QUOTEP))
     (7162 84
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (7099 88 (:DEFINITION APPLY$-BADGEP))
     (6825 147
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6804 63 (:DEFINITION RP::RP-TERMP))
     (5121 21 (:DEFINITION SUBSETP-EQUAL))
     (4848 294 (:DEFINITION MEMBER-EQUAL))
     (4655 4655 (:REWRITE DEFAULT-CDR))
     (4347 21 (:DEFINITION RP::FALIST-CONSISTENT))
     (3381 21
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3078 147
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2948 2948 (:REWRITE DEFAULT-CAR))
     (1554 1554 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (966 273 (:REWRITE O-P-O-INFP-CAR))
     (672 189 (:REWRITE RP::IS-IF-RP-TERMP))
     (651 651 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (508 42 (:DEFINITION NATP))
     (462 462 (:TYPE-PRESCRIPTION O-P))
     (462 462
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (441 441
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (357 357
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (328 328 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (294 294
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (273 84 (:REWRITE RP::RP-TERMP-CADR))
     (231 231 (:REWRITE O-P-DEF-O-FINP-1))
     (218 88 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (210 42 (:REWRITE RP::RP-TERMP-CADDDR))
     (189 189
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (189 63 (:REWRITE RP::RP-TERMP-CADDR))
     (189 63 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (175 145 (:REWRITE DEFAULT-+-2))
     (168 168 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (151 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (147 147 (:TYPE-PRESCRIPTION QUOTEP))
     (147 42
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (145 145 (:REWRITE DEFAULT-+-1))
     (126 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (126 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (126 21 (:DEFINITION ALL-NILS))
     (116 116 (:REWRITE ZP-OPEN))
     (105 105 (:TYPE-PRESCRIPTION ALL-NILS))
     (105 21
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (84 84 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (63 63
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (63 63
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (56 56 (:LINEAR LEN-WHEN-PREFIXP))
     (52 31 (:REWRITE DEFAULT-<-1))
     (42 42 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (42 42
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (40 31 (:REWRITE DEFAULT-<-2))
     (29 29 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (21 21
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (14 7
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (7 7
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (7 7
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::SORT-MEASURE-LEMMA1
     (101 56 (:REWRITE DEFAULT-PLUS-2))
     (66 56 (:REWRITE DEFAULT-PLUS-1))
     (36 36
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE DEFAULT-CDR))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (16 16 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (15 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 5 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(< (if a b c) x)|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::SORT-MEASURE-LEMMA1-V2
     (30 18 (:REWRITE DEFAULT-PLUS-2))
     (18 18 (:REWRITE DEFAULT-PLUS-1))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:LINEAR LEN-WHEN-PREFIXP))
     (12 12 (:REWRITE DEFAULT-CDR))
     (11 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 9 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 5 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE |(< (if a b c) x)|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::SORT-MEASURE-LEMMA2
     (6 3 (:REWRITE DEFAULT-PLUS-2))
     (5 5 (:REWRITE DEFAULT-CDR))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1 (:REWRITE |(< (if a b c) x)|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(RP::SORT-MEASURE-LEMMA2-V2-
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(RP::SORT-MEASURE-LEMMA3
     (665 665
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (665 665
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (665 665
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (665 665
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (468 36 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (324 36
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (324 36
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (180 36 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (180 36 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (180 36
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (180 36
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (180 36
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (180 36
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (180 36
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (33 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (32 32 (:REWRITE DEFAULT-TIMES-2))
     (32 32 (:REWRITE DEFAULT-TIMES-1))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (28 17 (:REWRITE DEFAULT-PLUS-2))
     (27 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (23 17 (:REWRITE DEFAULT-PLUS-1))
     (23 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (21 3 (:DEFINITION LEN))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (17 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 2 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5 (:META META-INTEGERP-CORRECT))
     (5 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE DEFAULT-FLOOR-1))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:LINEAR LEN-WHEN-PREFIXP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(RP::SORT-MEASURE-LEMMA4 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                         (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                         (13 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                         (9 1
                            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                         (9 1
                            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                         (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                         (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                         (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                         (5 1
                            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                         (5 1
                            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                         (5 1
                            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                         (5 1
                            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                         (5 1
                            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::LEN-OF-CUT-LIST-BY-HALF-SECOND
     (35 5 (:DEFINITION LEN))
     (15 10 (:REWRITE DEFAULT-PLUS-2))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (7 1 (:DEFINITION RP::CUT-LIST-BY-HALF))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (4 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-CAR)))
(RP::LEN-OF-CUT-LIST-BY-HALF-FIRST
     (21 3 (:DEFINITION LEN))
     (7 4 (:REWRITE DEFAULT-PLUS-2))
     (7 1 (:DEFINITION RP::CUT-LIST-BY-HALF))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-CAR)))
(RP::GUARD-LEMMA1
     (477 477
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (477 477
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (477 477
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (477 477
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (325 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (125 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (125 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (54 14 (:REWRITE DEFAULT-PLUS-2))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (33 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (29 29 (:REWRITE DEFAULT-TIMES-2))
     (29 29 (:REWRITE DEFAULT-TIMES-1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (23 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (22 22
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 14 (:REWRITE DEFAULT-PLUS-1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (10 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 4 (:REWRITE DEFAULT-MINUS))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:META META-INTEGERP-CORRECT))
     (5 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE DEFAULT-FLOOR-1))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(* (- x) y)|))
     (2 2 (:LINEAR LEN-WHEN-PREFIXP))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RP::O<-FLOOR
     (226 1 (:REWRITE O<=-O-FINP-DEF))
     (140 2 (:REWRITE |(< (+ c/d x) y)|))
     (113 1 (:REWRITE |(< (+ (- c) x) y)|))
     (82 3 (:REWRITE SIMPLIFY-SUMS-<))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (45 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (32 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (28 2 (:REWRITE |(+ y (+ x z))|))
     (23 8 (:REWRITE NORMALIZE-ADDENDS))
     (18 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (17 15 (:REWRITE DEFAULT-PLUS-1))
     (15 15 (:REWRITE DEFAULT-PLUS-2))
     (14 14 (:REWRITE DEFAULT-TIMES-2))
     (14 14 (:REWRITE DEFAULT-TIMES-1))
     (12 3 (:REWRITE |(* y x)|))
     (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 1 (:REWRITE |(+ y x)|))
     (8 1 (:REWRITE |(* x (+ y z))|))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (7 1 (:REWRITE |(* y (* x z))|))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 1 (:REWRITE O-INFP-O-FINP-O<=))
     (5 1 (:REWRITE AC-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:DEFINITION FIX))
     (4 1 (:REWRITE |(+ c (+ d x))|))
     (4 1 (:REWRITE |(+ (- x) (* c x))|))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(* a (/ a))|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(+ x (- x))|))
     (1 1 (:REWRITE |(+ 0 x)|))
     (1 1 (:REWRITE |(* a (/ a) b)|))
     (1 1 (:REWRITE |(* 1 x)|)))
(RP::O<-FLOOR-2 (187 1 (:REWRITE O<=-O-FINP-DEF))
                (101 2 (:REWRITE |(< (+ c/d x) y)|))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (56 3 (:REWRITE SIMPLIFY-SUMS-<))
                (53 17 (:REWRITE DEFAULT-PLUS-2))
                (32 4
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (21 17 (:REWRITE DEFAULT-PLUS-1))
                (18 18 (:REWRITE DEFAULT-TIMES-2))
                (18 18 (:REWRITE DEFAULT-TIMES-1))
                (16 8 (:REWRITE DEFAULT-LESS-THAN-1))
                (12 3 (:REWRITE |(* y x)|))
                (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
                (10 10
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (10 1 (:REWRITE |(+ y x)|))
                (8 8 (:REWRITE THE-FLOOR-BELOW))
                (8 8 (:REWRITE THE-FLOOR-ABOVE))
                (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
                (8 4 (:REWRITE DEFAULT-MINUS))
                (8 1 (:REWRITE |(* x (+ y z))|))
                (7 1 (:REWRITE |(* y (* x z))|))
                (5 5
                   (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (5 5
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
                (5 5
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (5 1 (:REWRITE O-INFP-O-FINP-O<=))
                (5 1 (:REWRITE AC-<))
                (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (4 4 (:REWRITE INTEGERP-<-CONSTANT))
                (4 4 (:REWRITE CONSTANT-<-INTEGERP))
                (4 4
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                (4 4
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                (4 4
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                (4 4
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                (4 4 (:REWRITE |(< c (- x))|))
                (4 4
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                (4 4
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                (4 4
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                (4 4
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                (4 4 (:REWRITE |(< (/ x) (/ y))|))
                (4 4 (:REWRITE |(< (- x) c)|))
                (4 4 (:REWRITE |(< (- x) (- y))|))
                (4 1 (:REWRITE |(+ (- x) (* c x))|))
                (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (2 2 (:REWRITE REDUCE-INTEGERP-+))
                (2 2 (:REWRITE INTEGERP-MINUS-X))
                (2 2
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (2 2 (:REWRITE |(* a (/ a))|))
                (2 2 (:REWRITE |(* (- x) y)|))
                (2 2 (:META META-INTEGERP-CORRECT))
                (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                (1 1 (:REWRITE DEFAULT-FLOOR-2))
                (1 1 (:REWRITE DEFAULT-FLOOR-1))
                (1 1 (:REWRITE |(floor x 2)| . 2))
                (1 1
                   (:REWRITE |(<= (/ x) y) with (< x 0)|))
                (1 1
                   (:REWRITE |(<= (/ x) y) with (< 0 x)|))
                (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
                (1 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
                (1 1 (:REWRITE |(< 0 (* x y))|))
                (1 1 (:REWRITE |(< (+ (- c) x) y)|))
                (1 1 (:REWRITE |(+ x (- x))|))
                (1 1 (:REWRITE |(* a (/ a) b)|))
                (1 1 (:REWRITE |(* 1 x)|)))
(RP::FLOOR-IS-POS (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (13 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (9 1
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (9 1
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (9 1
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                  (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (5 1
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::FLOOR-IS-LESS-THAN
     (693 693
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (693 693
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (693 693
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (693 693
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (368 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (272 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (272 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (272 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (56 8
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (33 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (32 32 (:REWRITE DEFAULT-TIMES-2))
     (32 32 (:REWRITE DEFAULT-TIMES-1))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (27 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (23 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (22 14 (:REWRITE DEFAULT-PLUS-2))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 14 (:REWRITE DEFAULT-PLUS-1))
     (16 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 2 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE DEFAULT-FLOOR-1))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(RP::CONSP-CDR-IMPLIES
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< x (if a b c))|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(RP::POS-LEN-IMPLIES (2 2 (:LINEAR LEN-WHEN-PREFIXP))
                     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::LESS-THAN-2-OF-LEN-IS
     (440 19 (:REWRITE RP::POS-LEN-IMPLIES))
     (32 16 (:REWRITE DEFAULT-PLUS-2))
     (22 22 (:REWRITE DEFAULT-CDR))
     (21 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (19 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (16 16 (:LINEAR LEN-WHEN-PREFIXP))
     (15 15 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (13 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE SIMPLIFY-SUMS-<))
     (11 11
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (11 11 (:REWRITE INTEGERP-<-CONSTANT))
     (11 11 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< c (- x))|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (11 11 (:REWRITE |(< (- x) c)|))
     (11 11 (:REWRITE |(< (- x) (- y))|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< 0 (/ x))|))
     (9 9 (:REWRITE |(< 0 (* x y))|))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE |(< x (if a b c))|))
     (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|))
     (1 1 (:REWRITE |(< (if a b c) x)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::MERGE-SORTED-AND$-LISTS (2481 5 (:REWRITE O<=-O-FINP-DEF))
                             (2102 8 (:LINEAR ACL2-COUNT-OF-SUM))
                             (1175 365 (:REWRITE DEFAULT-+-2))
                             (705 365 (:REWRITE DEFAULT-+-1))
                             (561 51 (:REWRITE RP::POS-LEN-IMPLIES))
                             (312 78 (:DEFINITION INTEGER-ABS))
                             (211 134 (:REWRITE DEFAULT-<-2))
                             (156 39 (:DEFINITION LENGTH))
                             (154 134 (:REWRITE DEFAULT-<-1))
                             (102 102 (:LINEAR LEN-WHEN-PREFIXP))
                             (91 91 (:REWRITE DEFAULT-CAR))
                             (90 90 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                             (85 85 (:REWRITE DEFAULT-CDR))
                             (79 5
                                 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
                             (78 78 (:REWRITE DEFAULT-UNARY-MINUS))
                             (78 39
                                 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                             (72 18 (:REWRITE O-P-O-INFP-CAR))
                             (51 5 (:REWRITE AC-<))
                             (39 39
                                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                             (39 39 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                             (39 39
                                 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                             (39 39
                                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                             (39 39
                                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                             (39 39 (:REWRITE DEFAULT-REALPART))
                             (39 39 (:REWRITE DEFAULT-NUMERATOR))
                             (39 39 (:REWRITE DEFAULT-IMAGPART))
                             (39 39 (:REWRITE DEFAULT-DENOMINATOR))
                             (25 5 (:REWRITE O-INFP-O-FINP-O<=))
                             (24 2 (:REWRITE <<-IMPLIES-LEXORDER))
                             (18 18
                                 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                             (16 4 (:REWRITE <<-TRICHOTOMY))
                             (13 13
                                 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                             (12 12 (:TYPE-PRESCRIPTION <<))
                             (10 10
                                 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                             (8 8
                                (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                             (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
                             (4 4 (:REWRITE <<-TRANSITIVE))
                             (4 2 (:REWRITE <<-ASYMMETRIC))
                             (2 2 (:REWRITE LEXORDER-TRANSITIVE)))
(RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS
     (109493 348
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (62359 138 (:DEFINITION RP::RP-TERMP))
     (61702 438
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (49054 114 (:DEFINITION RP::FALIST-CONSISTENT))
     (45656 203 (:DEFINITION RP::RP-TERM-LISTP))
     (40756 438
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (39679 438 (:DEFINITION QUOTEP))
     (38646 114
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (38515 213 (:DEFINITION APPLY$-BADGEP))
     (37492 3671 (:REWRITE RP::POS-LEN-IMPLIES))
     (35261 314
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (25672 24418 (:REWRITE DEFAULT-CDR))
     (25314 135 (:DEFINITION SUBSETP-EQUAL))
     (22590 1890 (:DEFINITION MEMBER-EQUAL))
     (14070 945
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (13423 11921 (:REWRITE DEFAULT-CAR))
     (6751 3578 (:REWRITE DEFAULT-<-2))
     (6640 6640 (:LINEAR LEN-WHEN-PREFIXP))
     (4800 1371 (:REWRITE O-P-O-INFP-CAR))
     (4185 4185 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (3578 3578
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3578 3578 (:REWRITE DEFAULT-<-1))
     (3574 143
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2835 2835
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (2682 270 (:DEFINITION NATP))
     (2322 213 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1890 1890
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1839 117
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1779 135 (:DEFINITION ALL-NILS))
     (1719 1719 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (1674 639 (:REWRITE RP::IS-IF-RP-TERMP))
     (1665 630
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (1370 1370
           (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (1143 1143 (:REWRITE O-P-DEF-O-FINP-1))
     (1056 1056
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1026 1026
           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (960 351 (:REWRITE RP::RP-TERMP-CADR))
     (880 880 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (810 405
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (675 675 (:TYPE-PRESCRIPTION ALL-NILS))
     (554 248 (:REWRITE RP::RP-TERMP-CADDR))
     (554 248 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (540 540 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (438 438 (:TYPE-PRESCRIPTION QUOTEP))
     (411 187
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (405 405
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (348 348
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (228 228
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (160 40 (:REWRITE RP::RP-TERMP-CADDDR))
     (126 11 (:REWRITE <<-IMPLIES-LEXORDER))
     (117 117
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (82 21 (:REWRITE <<-TRICHOTOMY))
     (62 62 (:TYPE-PRESCRIPTION <<))
     (21 21 (:REWRITE <<-TRANSITIVE))
     (20 10 (:REWRITE <<-ASYMMETRIC))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::SORT-AND$-LIST (23 23 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                    (13 9 (:REWRITE DEFAULT-CDR))
                    (11 7 (:REWRITE DEFAULT-<-2))
                    (8 8 (:LINEAR LEN-WHEN-PREFIXP))
                    (8 7 (:REWRITE DEFAULT-<-1))
                    (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                    (2 1 (:REWRITE DEFAULT-+-2))
                    (1 1 (:REWRITE DEFAULT-+-1)))
(RP::TRUE-LISTP-OF-SORT-AND$-LIST
     (80233 255
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (45246 109 (:DEFINITION RP::RP-TERMP))
     (43165 336
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (35201 151 (:DEFINITION RP::RP-TERM-LISTP))
     (34384 93 (:DEFINITION RP::FALIST-CONSISTENT))
     (30390 336
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (29438 336 (:DEFINITION QUOTEP))
     (28785 160 (:DEFINITION APPLY$-BADGEP))
     (26787 85
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (25293 234
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (18781 17598 (:REWRITE DEFAULT-CDR))
     (18556 98 (:DEFINITION SUBSETP-EQUAL))
     (16572 1372 (:DEFINITION MEMBER-EQUAL))
     (10479 8592 (:REWRITE DEFAULT-CAR))
     (10324 686
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (4918 2606 (:REWRITE DEFAULT-<-2))
     (4880 4880 (:LINEAR LEN-WHEN-PREFIXP))
     (3612 106
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (3490 969 (:REWRITE O-P-O-INFP-CAR))
     (3038 3038 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2735 2735
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2606 2606 (:REWRITE DEFAULT-<-1))
     (2139 160 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (2058 2058
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1966 196 (:DEFINITION NATP))
     (1623 100
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1378 467
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (1372 1372
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1298 98 (:DEFINITION ALL-NILS))
     (1275 1275 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (1266 474 (:REWRITE RP::IS-IF-RP-TERMP))
     (1013 1013
           (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (899 811 (:REWRITE O-P-DEF-O-FINP-1))
     (798 798
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (711 711
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (688 252 (:REWRITE RP::RP-TERMP-CADR))
     (634 634 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (588 294
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (490 490 (:TYPE-PRESCRIPTION ALL-NILS))
     (450 190 (:REWRITE RP::RP-TERMP-CADDR))
     (450 190 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (392 392 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (336 336 (:TYPE-PRESCRIPTION QUOTEP))
     (324 142
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (294 294
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (255 255
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (186 186
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (128 32 (:REWRITE RP::RP-TERMP-CADDDR))
     (126 11 (:REWRITE <<-IMPLIES-LEXORDER))
     (100 100
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (88 88 (:TYPE-PRESCRIPTION O-FINP))
     (82 21 (:REWRITE <<-TRICHOTOMY))
     (62 62 (:TYPE-PRESCRIPTION <<))
     (40 40 (:TYPE-PRESCRIPTION FLOOR))
     (40 20 (:REWRITE DEFAULT-UNARY-MINUS))
     (40 20 (:REWRITE DEFAULT-+-2))
     (21 21 (:REWRITE <<-TRANSITIVE))
     (20 20 (:REWRITE DEFAULT-+-1))
     (20 10 (:REWRITE <<-ASYMMETRIC))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::SORT-AND$-LIST
     (27164 64
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (17670 54 (:DEFINITION APPLY$-BADGEP))
     (13592 27
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (13510 7 (:DEFINITION RP::RP-TERMP))
     (13151 27
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (13077 27 (:DEFINITION QUOTEP))
     (12030 623
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11644 476 (:REWRITE ACL2-NUMBERP-X))
     (11092 13 (:DEFINITION RP::RP-TERM-LISTP))
     (10093 215 (:REWRITE RATIONALP-X))
     (9744 36 (:DEFINITION SUBSETP-EQUAL))
     (9483 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (8848 254 (:DEFINITION MEMBER-EQUAL))
     (8271 159
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (7935 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (7342 101
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (5423 4 (:DEFINITION RP::SORT-AND$-LIST))
     (3478 252
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3205 2844 (:REWRITE DEFAULT-CDR))
     (1986 1111 (:REWRITE DEFAULT-CAR))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1596 40
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1530 54 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1089 623
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (907 97
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (756 756
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (751 623 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (666 666 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (644 36 (:DEFINITION ALL-NILS))
     (629 625
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (625 625
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (623 623
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (623 623 (:REWRITE |(equal c (/ x))|))
     (623 623 (:REWRITE |(equal c (- x))|))
     (623 623 (:REWRITE |(equal (/ x) c)|))
     (623 623 (:REWRITE |(equal (/ x) (/ y))|))
     (623 623 (:REWRITE |(equal (- x) c)|))
     (623 623 (:REWRITE |(equal (- x) (- y))|))
     (531 159 (:REWRITE DEFAULT-PLUS-2))
     (521 521 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (504 504
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (498 306 (:REWRITE DEFAULT-LESS-THAN-2))
     (496 496 (:LINEAR LEN-WHEN-PREFIXP))
     (477 290
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (476 476
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (472 114
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (374 4 (:REWRITE |(+ x (if a b c))|))
     (334 290
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (329 307 (:REWRITE REDUCE-INTEGERP-+))
     (325 325
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (322 7
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (308 306 (:REWRITE DEFAULT-LESS-THAN-1))
     (307 307 (:REWRITE INTEGERP-MINUS-X))
     (307 307
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (307 307 (:META META-INTEGERP-CORRECT))
     (306 306 (:REWRITE THE-FLOOR-BELOW))
     (306 306 (:REWRITE THE-FLOOR-ABOVE))
     (302 84 (:REWRITE O-P-O-INFP-CAR))
     (300 300
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (300 300
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (296 292
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (295 295 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (292 292 (:REWRITE INTEGERP-<-CONSTANT))
     (292 292 (:REWRITE CONSTANT-<-INTEGERP))
     (292 292
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (292 292
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (292 292
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (292 292
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (292 292 (:REWRITE |(< c (- x))|))
     (292 292
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (292 292
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (292 292
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (292 292
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (292 292 (:REWRITE |(< (/ x) (/ y))|))
     (292 292 (:REWRITE |(< (- x) c)|))
     (292 292 (:REWRITE |(< (- x) (- y))|))
     (290 290 (:REWRITE SIMPLIFY-SUMS-<))
     (263 217
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (231 231 (:REWRITE |(< 0 (* x y))|))
     (217 217 (:REWRITE |(< 0 (/ x))|))
     (216 216
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (215 215 (:REWRITE REDUCE-RATIONALP-+))
     (215 215 (:REWRITE REDUCE-RATIONALP-*))
     (215 215 (:REWRITE RATIONALP-MINUS-X))
     (215 215
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (215 215 (:META META-RATIONALP-CORRECT))
     (212 4 (:REWRITE |(+ (+ x y) z)|))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (180 180 (:TYPE-PRESCRIPTION ALL-NILS))
     (175 159 (:REWRITE DEFAULT-PLUS-1))
     (156 4 (:REWRITE |(- (if a b c))|))
     (144 144 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (142 142 (:REWRITE DEFAULT-TIMES-2))
     (142 142 (:REWRITE DEFAULT-TIMES-1))
     (127 127
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (108 41 (:REWRITE RP::IS-IF-RP-TERMP))
     (103 5 (:REWRITE DEFAULT-FLOOR-RATIO))
     (102 102
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (90 34 (:REWRITE DEFAULT-MINUS))
     (84 84
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (78 70 (:REWRITE O-P-DEF-O-FINP-1))
     (69 69 (:REWRITE |(< (/ x) 0)|))
     (69 69 (:REWRITE |(< (* x y) 0)|))
     (66 66
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (64 64
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (64 64
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (64 16 (:REWRITE |(* c (* d x))|))
     (63 63
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (56 21 (:REWRITE RP::RP-TERMP-CADR))
     (55 55 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (50 5 (:REWRITE |(* y x)|))
     (48 4 (:REWRITE <<-IMPLIES-LEXORDER))
     (42 42 (:REWRITE |(equal x (if a b c))|))
     (42 42 (:REWRITE |(equal (if a b c) x)|))
     (36 16 (:REWRITE RP::RP-TERMP-CADDR))
     (36 16 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (32 8 (:REWRITE <<-TRICHOTOMY))
     (32 8 (:REWRITE |(+ (* c x) (* d x))|))
     (27 27 (:TYPE-PRESCRIPTION QUOTEP))
     (26 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (26 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (26 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (26 26 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (26 26
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (26 2 (:REWRITE RP::SORT-MEASURE-LEMMA1))
     (26 2 (:REWRITE |(* (* x y) z)|))
     (24 24 (:TYPE-PRESCRIPTION <<))
     (20 4 (:REWRITE RP::SORT-MEASURE-LEMMA1-V2))
     (18 18 (:REWRITE |(* (- x) y)|))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (16 4 (:REWRITE RP::RP-TERMP-CADDDR))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 2 (:REWRITE |(+ y x)|))
     (8 8 (:TYPE-PRESCRIPTION O-FINP))
     (8 8 (:REWRITE <<-TRANSITIVE))
     (8 4 (:REWRITE <<-ASYMMETRIC))
     (7 7
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE DEFAULT-FLOOR-1))
     (5 5 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:TYPE-PRESCRIPTION LEXORDER))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE LEXORDER-TRANSITIVE))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (2 2
        (:REWRITE |(not (equal (* (/ x) y) 1))|))
     (2 2 (:REWRITE |(floor (+ x r) i)|)))
(RP::PP-LISTS-P-IMPLIES-ALISTP
     (5574 15
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (4902 5 (:DEFINITION TRUE-LISTP))
     (3288 15 (:DEFINITION RP::RP-TERMP))
     (3158 47
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2370 16 (:DEFINITION RP::RP-TERM-LISTP))
     (2170 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (2113 47
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1966 185 (:REWRITE RP::POS-LEN-IMPLIES))
     (1832 47 (:DEFINITION QUOTEP))
     (1695 38 (:DEFINITION APPLY$-BADGEP))
     (1695 5
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1692 26
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1144 1089 (:REWRITE DEFAULT-CDR))
     (1100 5 (:DEFINITION SUBSETP-EQUAL))
     (1000 70 (:DEFINITION MEMBER-EQUAL))
     (816 741 (:REWRITE DEFAULT-CAR))
     (630 35
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (345 180 (:REWRITE DEFAULT-<-2))
     (340 340 (:LINEAR LEN-WHEN-PREFIXP))
     (246 69 (:REWRITE O-P-O-INFP-CAR))
     (180 180
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (180 180 (:REWRITE DEFAULT-<-1))
     (172 51 (:REWRITE RP::IS-IF-RP-TERMP))
     (160 38 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (155 155 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (122 122
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (121 10 (:DEFINITION NATP))
     (112 112 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (111 35
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (109 109
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (105 105
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (80 5
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (77 26 (:REWRITE RP::RP-TERMP-CADR))
     (70 70
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (65 5 (:DEFINITION ALL-NILS))
     (59 59 (:REWRITE O-P-DEF-O-FINP-1))
     (50 10 (:REWRITE RP::RP-TERMP-CADDDR))
     (47 47 (:TYPE-PRESCRIPTION QUOTEP))
     (46 46 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (45 45
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (45 15 (:REWRITE RP::RP-TERMP-CADDR))
     (45 15 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (36 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (35 10
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
     (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (15 15
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (15 15
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::MERGE-SORTED-PP-LISTS (3860 5 (:REWRITE O<=-O-FINP-DEF))
                           (3440 10 (:LINEAR ACL2-COUNT-OF-SUM))
                           (1739 537 (:REWRITE DEFAULT-+-2))
                           (1043 537 (:REWRITE DEFAULT-+-1))
                           (1001 91 (:REWRITE RP::POS-LEN-IMPLIES))
                           (480 120 (:DEFINITION INTEGER-ABS))
                           (340 130 (:REWRITE DEFAULT-CDR))
                           (339 216 (:REWRITE DEFAULT-<-2))
                           (240 60 (:DEFINITION LENGTH))
                           (236 216 (:REWRITE DEFAULT-<-1))
                           (226 136 (:REWRITE DEFAULT-CAR))
                           (204 51 (:REWRITE O-P-O-INFP-CAR))
                           (182 182 (:LINEAR LEN-WHEN-PREFIXP))
                           (151 151
                                (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                           (120 120 (:REWRITE DEFAULT-UNARY-MINUS))
                           (120 60
                                (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                           (80 5
                               (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
                           (60 60
                               (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                           (60 60 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                           (60 60
                               (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                           (60 60
                               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                           (60 60
                               (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                           (60 60 (:REWRITE DEFAULT-REALPART))
                           (60 60 (:REWRITE DEFAULT-NUMERATOR))
                           (60 60 (:REWRITE DEFAULT-IMAGPART))
                           (60 60 (:REWRITE DEFAULT-DENOMINATOR))
                           (57 5 (:REWRITE AC-<))
                           (25 5 (:REWRITE O-INFP-O-FINP-O<=))
                           (20 20
                               (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                           (15 15
                               (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                           (10 10
                               (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                           (10 10
                               (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                           (5 5
                              (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::PP-LISTS-P-OF-MERGE-SORTED-PP-LISTS
     (4290 390 (:REWRITE RP::POS-LEN-IMPLIES))
     (780 780 (:LINEAR LEN-WHEN-PREFIXP))
     (780 390 (:REWRITE DEFAULT-<-2))
     (656 164 (:REWRITE O-P-O-INFP-CAR))
     (390 390
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (390 390 (:REWRITE DEFAULT-<-1))
     (164 164 (:REWRITE O-P-DEF-O-FINP-1))
     (124 124
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP)))
(RP::MERGE-SORTED-PP-LISTS (1023 93 (:REWRITE RP::POS-LEN-IMPLIES))
                           (352 6
                                (:DEFINITION RP::MERGE-SORTED-PP-LISTS))
                           (280 24 (:DEFINITION ACONS))
                           (256 16 (:REWRITE CONS-CAR-CDR))
                           (236 59 (:REWRITE O-P-O-INFP-CAR))
                           (186 186 (:LINEAR LEN-WHEN-PREFIXP))
                           (186 93 (:REWRITE DEFAULT-<-2))
                           (93 93 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                           (93 93 (:REWRITE DEFAULT-<-1))
                           (59 59 (:REWRITE O-P-DEF-O-FINP-1))
                           (41 41
                               (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                           (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
                           (4 4 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::SORT-PP-LISTS (21500 4 (:DEFINITION RP::EX-FROM-RP))
                   (20646 8 (:DEFINITION APPLY$-BADGEP))
                   (19592 1740 (:REWRITE RP::MEASURE-LEMMA1))
                   (15234 1504 (:REWRITE RP::SORT-MEASURE-LEMMA2))
                   (14070 16
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (13550 8 (:DEFINITION TRUE-LISTP))
                   (12356 46
                          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (12350 4 (:REWRITE RP::NOT-INCLUDE-RP))
                   (12338 4 (:DEFINITION RP::INCLUDE-FNC))
                   (11900 40
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (11836 24 (:DEFINITION RP::RP-TERMP))
                   (10062 1268 (:REWRITE RP::MEASURE-LEMMA1-2))
                   (9988 8 (:DEFINITION RP::FALIST-CONSISTENT))
                   (8963 1869 (:REWRITE DEFAULT-CDR))
                   (8524 98
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (8221 429
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                   (7648 8
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (6490 868 (:REWRITE DEFAULT-CAR))
                   (6194 122 (:REWRITE LEN-WHEN-PREFIXP))
                   (3524 120
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                   (3302 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (2034 16 (:DEFINITION RP::RP-TERM-LISTP))
                   (1722 8 (:DEFINITION SUBSETP-EQUAL))
                   (1712 1712 (:LINEAR LEN-WHEN-PREFIXP))
                   (1708 120
                         (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                   (1348 112 (:DEFINITION MEMBER-EQUAL))
                   (1041 429
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                   (840 56
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (731 731
                        (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (703 429 (:REWRITE DEFAULT-<-2))
                   (696 696 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                   (552 429 (:REWRITE DEFAULT-<-1))
                   (350 128 (:REWRITE O-P-O-INFP-CAR))
                   (336 40
                        (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (320 96 (:REWRITE RP::IS-IF-RP-TERMP))
                   (318 8 (:DEFINITION ALL-NILS))
                   (248 248 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (236 236 (:TYPE-PRESCRIPTION PREFIXP))
                   (218 218 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (216 16 (:DEFINITION NATP))
                   (212 44 (:DEFINITION QUOTEP))
                   (198 8
                        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (168 168
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (149 149
                        (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                   (128 32 (:REWRITE RP::RP-TERMP-CADDDR))
                   (124 116
                        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                   (120 120 (:REWRITE PREFIXP-TRANSITIVE . 2))
                   (120 120 (:REWRITE PREFIXP-TRANSITIVE . 1))
                   (120 120
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                   (120 120
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                   (112 112
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (96 96
                       (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                   (96 96
                       (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (96 32 (:REWRITE RP::RP-TERMP-CADR))
                   (96 32 (:REWRITE RP::RP-TERMP-CADDR))
                   (96 32 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (80 36
                       (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (72 72
                       (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                   (64 64 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (40 40 (:TYPE-PRESCRIPTION QUOTEP))
                   (40 40 (:TYPE-PRESCRIPTION ALL-NILS))
                   (36 18
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
                   (32 32 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (24 10
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (20 20
                       (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                   (18 18
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (16 16
                       (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                   (12 12 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                   (8 8
                      (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                   (8 8
                      (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                   (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                   (2 1 (:REWRITE DEFAULT-+-2))
                   (1 1 (:REWRITE DEFAULT-+-1)))
(RP::PP-LISTS-P-OF-SORT-PP-LISTS
     (49946 123
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (44388 41 (:DEFINITION TRUE-LISTP))
     (27140 135 (:DEFINITION RP::RP-TERMP))
     (25986 369
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (23416 128 (:DEFINITION RP::RP-TERM-LISTP))
     (21359 369
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (18952 369 (:DEFINITION QUOTEP))
     (17871 296 (:DEFINITION APPLY$-BADGEP))
     (17840 210
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (17794 41 (:DEFINITION RP::FALIST-CONSISTENT))
     (13899 41
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (13014 41 (:DEFINITION SUBSETP-EQUAL))
     (12194 574 (:DEFINITION MEMBER-EQUAL))
     (7796 287
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3235 1679 (:REWRITE DEFAULT-<-2))
     (3138 3138 (:LINEAR LEN-WHEN-PREFIXP))
     (2593 723 (:REWRITE O-P-O-INFP-CAR))
     (1716 1716
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1679 1679 (:REWRITE DEFAULT-<-1))
     (1636 517 (:REWRITE RP::IS-IF-RP-TERMP))
     (1287 296 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1271 1271 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1088 1088
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (986 82 (:DEFINITION NATP))
     (940 940 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (904 287
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (861 861
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (859 859
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (797 312 (:REWRITE RP::RP-TERMP-CADR))
     (750 560 (:REWRITE O-P-DEF-O-FINP-1))
     (656 41
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (574 574
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (533 41 (:DEFINITION ALL-NILS))
     (470 82 (:REWRITE RP::RP-TERMP-CADDDR))
     (399 123 (:REWRITE RP::RP-TERMP-CADDR))
     (399 123 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (374 374 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (369 369 (:TYPE-PRESCRIPTION QUOTEP))
     (369 369
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (289 123
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (287 82
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (246 123
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (205 205 (:TYPE-PRESCRIPTION ALL-NILS))
     (190 190 (:TYPE-PRESCRIPTION O-FINP))
     (164 164 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (123 123
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (123 123
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (82 82
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (78 39 (:REWRITE DEFAULT-UNARY-MINUS))
     (78 39 (:REWRITE DEFAULT-+-2))
     (41 41
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (39 39 (:REWRITE DEFAULT-+-1)))
(RP::SORT-PP-LISTS (4880 15
                         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (4626 5 (:DEFINITION TRUE-LISTP))
                   (2850 28
                         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (2826 11 (:DEFINITION RP::RP-TERMP))
                   (2140 5 (:DEFINITION RP::FALIST-CONSISTENT))
                   (1930 9 (:DEFINITION RP::RP-TERM-LISTP))
                   (1768 28
                         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (1695 5
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (1654 28 (:DEFINITION QUOTEP))
                   (1567 20 (:DEFINITION APPLY$-BADGEP))
                   (1562 16
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (1166 1077 (:REWRITE DEFAULT-CDR))
                   (1032 5 (:DEFINITION SUBSETP-EQUAL))
                   (932 70 (:DEFINITION MEMBER-EQUAL))
                   (931 624 (:REWRITE DEFAULT-CAR))
                   (584 35
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (346 2 (:DEFINITION RP::SORT-PP-LISTS))
                   (338 178 (:REWRITE DEFAULT-<-2))
                   (320 320 (:LINEAR LEN-WHEN-PREFIXP))
                   (290 290 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                   (286 79 (:REWRITE O-P-O-INFP-CAR))
                   (215 215
                        (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (180 178 (:REWRITE DEFAULT-<-1))
                   (155 155 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (123 20 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (120 37 (:REWRITE RP::IS-IF-RP-TERMP))
                   (105 105
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (88 88 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (85 61 (:REWRITE O-P-DEF-O-FINP-1))
                   (84 5
                       (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (83 83
                       (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (82 29
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (72 72
                       (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                   (70 70
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (65 5 (:DEFINITION ALL-NILS))
                   (55 18 (:REWRITE RP::RP-TERMP-CADR))
                   (45 45
                       (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                   (39 39 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (35 13 (:REWRITE RP::RP-TERMP-CADDR))
                   (35 13 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (30 15
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (30 6 (:REWRITE RP::RP-TERMP-CADDDR))
                   (28 28 (:TYPE-PRESCRIPTION QUOTEP))
                   (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
                   (25 11
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (25 8
                       (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (24 24 (:TYPE-PRESCRIPTION O-FINP))
                   (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (19 9 (:REWRITE DEFAULT-+-2))
                   (16 8 (:REWRITE DEFAULT-UNARY-MINUS))
                   (15 15
                       (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                   (15 15
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (11 9 (:REWRITE DEFAULT-+-1))
                   (10 10
                       (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                   (10 2 (:REWRITE RP::SORT-MEASURE-LEMMA1-V2))
                   (10 1 (:REWRITE ASSOCIATIVITY-OF-+))
                   (5 5
                      (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                   (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::AND$-PP-LISTS-AUX
     (8182 34
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (7096 11 (:DEFINITION TRUE-LISTP))
     (4453 67
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (4332 20 (:DEFINITION RP::RP-TERM-LISTP))
     (4068 66 (:DEFINITION QUOTEP))
     (3832 37 (:DEFINITION APPLY$-BADGEP))
     (3592 42
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3294 28 (:DEFINITION RP::RP-TERMP))
     (3219 67
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2741 13 (:DEFINITION SUBSETP-EQUAL))
     (2572 182 (:DEFINITION MEMBER-EQUAL))
     (2481 2433 (:REWRITE DEFAULT-CDR))
     (2092 12 (:DEFINITION RP::FALIST-CONSISTENT))
     (1618 91
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1610 10
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1444 1444 (:REWRITE DEFAULT-CAR))
     (530 149 (:REWRITE O-P-O-INFP-CAR))
     (403 403 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (403 101 (:REWRITE RP::IS-IF-RP-TERMP))
     (342 21
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (292 26 (:DEFINITION NATP))
     (273 273
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (222 222
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (211 52 (:REWRITE RP::RP-TERMP-CADR))
     (182 182
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (170 170
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (170 170 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (127 127 (:REWRITE O-P-DEF-O-FINP-1))
     (112 37 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (98 31 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (96 18 (:REWRITE RP::RP-TERMP-CADDDR))
     (92 31 (:REWRITE RP::RP-TERMP-CADDR))
     (90 90
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (82 82 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (78 78 (:TYPE-PRESCRIPTION LEN))
     (78 39
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (78 13 (:DEFINITION ALL-NILS))
     (73 32
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (66 66 (:TYPE-PRESCRIPTION QUOTEP))
     (65 65 (:TYPE-PRESCRIPTION ALL-NILS))
     (60 12
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (54 27
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (52 52 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (39 39
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (34 34
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (28 28 (:LINEAR LEN-WHEN-PREFIXP))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (13 13 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (13 13 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 2
        (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS)))
(RP::PP-LISTS-P-OF-AND$-PP-LISTS-AUX
     (32046 132
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (28578 44 (:DEFINITION TRUE-LISTP))
     (16572 94 (:DEFINITION RP::RP-TERM-LISTP))
     (15798 294
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (14410 124 (:DEFINITION RP::RP-TERMP))
     (14256 294 (:DEFINITION QUOTEP))
     (14199 294
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (13318 162
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (13157 159 (:DEFINITION APPLY$-BADGEP))
     (9425 9423 (:REWRITE DEFAULT-CDR))
     (9281 44 (:DEFINITION SUBSETP-EQUAL))
     (9207 48 (:DEFINITION RP::FALIST-CONSISTENT))
     (8709 616 (:DEFINITION MEMBER-EQUAL))
     (7139 44
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (5671 5667 (:REWRITE DEFAULT-CAR))
     (5487 308
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2000 566 (:REWRITE O-P-O-INFP-CAR))
     (1526 436 (:REWRITE RP::IS-IF-RP-TERMP))
     (1364 1364 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1103 88 (:DEFINITION NATP))
     (928 928
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (924 924
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (782 242 (:REWRITE RP::RP-TERMP-CADR))
     (740 740
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (616 616
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (592 592 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (500 500
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (478 478 (:REWRITE O-P-DEF-O-FINP-1))
     (417 159 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (396 396
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (384 126 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (376 68 (:REWRITE RP::RP-TERMP-CADDDR))
     (372 126 (:REWRITE RP::RP-TERMP-CADDR))
     (362 362 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (299 112
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (294 294 (:TYPE-PRESCRIPTION QUOTEP))
     (291 132
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (276 78
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (264 264 (:TYPE-PRESCRIPTION LEN))
     (264 44 (:DEFINITION ALL-NILS))
     (240 48
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (220 220 (:TYPE-PRESCRIPTION ALL-NILS))
     (194 88
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (176 176 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (132 132
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (132 132
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (96 96
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (88 88 (:LINEAR LEN-WHEN-PREFIXP))
     (48 48
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (44 44 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (44 44 (:REWRITE DEFAULT-<-2))
     (44 44 (:REWRITE DEFAULT-<-1)))
(RP::AND$-PP-LISTS (40655 160
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (36220 53 (:DEFINITION TRUE-LISTP))
                   (21927 108 (:DEFINITION RP::RP-TERM-LISTP))
                   (21167 360
                          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (19430 359 (:DEFINITION QUOTEP))
                   (18097 205 (:DEFINITION APPLY$-BADGEP))
                   (18009 208
                          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (17032 154 (:DEFINITION RP::RP-TERMP))
                   (16931 360
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (13244 55 (:DEFINITION SUBSETP-EQUAL))
                   (12529 770 (:DEFINITION MEMBER-EQUAL))
                   (12296 11796 (:REWRITE DEFAULT-CDR))
                   (10831 54 (:DEFINITION RP::FALIST-CONSISTENT))
                   (8417 52
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (7951 385
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (7569 7452 (:REWRITE DEFAULT-CAR))
                   (3019 919 (:REWRITE O-P-O-INFP-CAR))
                   (1770 504 (:REWRITE RP::IS-IF-RP-TERMP))
                   (1705 1705 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (1364 110 (:DEFINITION NATP))
                   (1155 1155
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (1148 1148
                         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (888 888
                        (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                   (807 254 (:REWRITE RP::RP-TERMP-CADR))
                   (776 776 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (770 770
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (700 700 (:REWRITE O-P-DEF-O-FINP-1))
                   (635 102
                        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (541 205 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (504 96 (:REWRITE RP::RP-TERMP-CADDDR))
                   (470 154 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (468 468
                        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                   (464 154 (:REWRITE RP::RP-TERMP-CADDR))
                   (422 422 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (387 152
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (376 376
                        (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
                   (359 359 (:TYPE-PRESCRIPTION QUOTEP))
                   (351 165
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (330 330 (:TYPE-PRESCRIPTION LEN))
                   (330 55 (:DEFINITION ALL-NILS))
                   (275 275 (:TYPE-PRESCRIPTION ALL-NILS))
                   (270 54
                        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (236 111
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (220 220 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (165 165
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (160 160
                        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                   (112 112 (:LINEAR LEN-WHEN-PREFIXP))
                   (108 108
                        (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                   (55 55 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (55 55 (:REWRITE DEFAULT-<-2))
                   (55 55 (:REWRITE DEFAULT-<-1))
                   (54 54
                       (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::PP-LISTS-P-OF-AND$-PP-LISTS
     (34437 135
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (30293 45 (:DEFINITION TRUE-LISTP))
     (17909 96 (:DEFINITION RP::RP-TERM-LISTP))
     (17180 331
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (15385 331 (:DEFINITION QUOTEP))
     (15270 147 (:DEFINITION RP::RP-TERMP))
     (14958 331
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (14307 186
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (14127 195 (:DEFINITION APPLY$-BADGEP))
     (9988 45 (:DEFINITION SUBSETP-EQUAL))
     (9874 9874 (:REWRITE DEFAULT-CDR))
     (9424 49 (:DEFINITION RP::FALIST-CONSISTENT))
     (9403 630 (:DEFINITION MEMBER-EQUAL))
     (7310 45
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (6249 6249 (:REWRITE DEFAULT-CAR))
     (5943 315
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2086 589 (:REWRITE O-P-O-INFP-CAR))
     (1758 485 (:REWRITE RP::IS-IF-RP-TERMP))
     (1395 1395 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1199 90 (:DEFINITION NATP))
     (1080 1080
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (945 945
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (845 256 (:REWRITE RP::RP-TERMP-CADR))
     (797 797
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (663 663 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (630 630
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (545 545
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (499 499 (:REWRITE O-P-DEF-O-FINP-1))
     (493 195 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (486 90 (:REWRITE RP::RP-TERMP-CADDDR))
     (443 139 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (431 139 (:REWRITE RP::RP-TERMP-CADDR))
     (405 405
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (370 370 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (366 135
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (337 90
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (331 331 (:TYPE-PRESCRIPTION QUOTEP))
     (303 135
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (270 270 (:TYPE-PRESCRIPTION LEN))
     (270 45 (:DEFINITION ALL-NILS))
     (245 49
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (225 225 (:TYPE-PRESCRIPTION ALL-NILS))
     (202 90
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (180 180 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (135 135
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (135 135
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (98 98
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (94 47
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (90 90 (:LINEAR LEN-WHEN-PREFIXP))
     (49 49
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (45 45 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (45 45 (:REWRITE DEFAULT-<-2))
     (45 45 (:REWRITE DEFAULT-<-1)))
(RP::APPEND-OF-PP-LIST-P
     (8832 36
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (7908 12 (:DEFINITION TRUE-LISTP))
     (4602 24 (:DEFINITION RP::RP-TERM-LISTP))
     (4362 84
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (3993 84 (:DEFINITION QUOTEP))
     (3885 84
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3876 36 (:DEFINITION RP::RP-TERMP))
     (3729 48
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3693 51 (:DEFINITION APPLY$-BADGEP))
     (2646 12 (:DEFINITION SUBSETP-EQUAL))
     (2642 2618 (:REWRITE DEFAULT-CDR))
     (2490 168 (:DEFINITION MEMBER-EQUAL))
     (2484 12 (:DEFINITION RP::FALIST-CONSISTENT))
     (1932 12
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1690 1681 (:REWRITE DEFAULT-CAR))
     (1572 84
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (540 153 (:REWRITE O-P-O-INFP-CAR))
     (372 372 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (372 108 (:REWRITE RP::IS-IF-RP-TERMP))
     (291 24 (:DEFINITION NATP))
     (258 258 (:TYPE-PRESCRIPTION O-P))
     (252 252
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (231 231
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (204 204
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (174 174 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (168 168
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (153 48 (:REWRITE RP::RP-TERMP-CADR))
     (129 129 (:REWRITE O-P-DEF-O-FINP-1))
     (126 51 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (114 24 (:REWRITE RP::RP-TERMP-CADDDR))
     (108 108
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (105 36 (:REWRITE RP::RP-TERMP-CADDR))
     (105 36 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (96 96 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (87 36
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (84 84 (:TYPE-PRESCRIPTION QUOTEP))
     (84 24
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (72 72 (:TYPE-PRESCRIPTION LEN))
     (72 36
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (72 12 (:DEFINITION ALL-NILS))
     (60 60 (:TYPE-PRESCRIPTION ALL-NILS))
     (60 12
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (48 48 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (48 24
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (41 41 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (36 36
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (36 36
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (34 17
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (27 9 (:REWRITE CAR-OF-APPEND))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (17 17 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (12 12 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE CONSP-OF-APPEND))
     (5 5 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(RP::PP-LISTS-P-IMPLIES-TRUE-LISTP
     (3364 15
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (3092 5 (:DEFINITION TRUE-LISTP))
     (1730 10 (:DEFINITION RP::RP-TERM-LISTP))
     (1613 29
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1541 29
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1516 11 (:DEFINITION RP::RP-TERMP))
     (1502 29 (:DEFINITION QUOTEP))
     (1414 16
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1401 15 (:DEFINITION APPLY$-BADGEP))
     (1035 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (1030 1030 (:REWRITE DEFAULT-CDR))
     (993 5 (:DEFINITION SUBSETP-EQUAL))
     (928 70 (:DEFINITION MEMBER-EQUAL))
     (805 5
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (599 599 (:REWRITE DEFAULT-CAR))
     (582 35
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (222 63 (:REWRITE O-P-O-INFP-CAR))
     (155 155 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (120 37 (:REWRITE RP::IS-IF-RP-TERMP))
     (111 10 (:DEFINITION NATP))
     (106 106 (:TYPE-PRESCRIPTION O-P))
     (105 105
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (84 84
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (77 77
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (70 70
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (61 61 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (55 18 (:REWRITE RP::RP-TERMP-CADR))
     (53 53 (:REWRITE O-P-DEF-O-FINP-1))
     (45 45
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (40 40 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (40 15 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (35 13 (:REWRITE RP::RP-TERMP-CADDR))
     (35 13 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (30 30 (:TYPE-PRESCRIPTION LEN))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (30 6 (:REWRITE RP::RP-TERMP-CADDDR))
     (30 5 (:DEFINITION ALL-NILS))
     (29 29 (:TYPE-PRESCRIPTION QUOTEP))
     (26 11
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
     (25 8
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (25 5
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (20 10
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (15 15
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (15 15
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10 (:LINEAR LEN-WHEN-PREFIXP))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1)))
(RP::APPLY-SIGN-TO-PP-LISTS)
(RP::PP-LISTS-P-OF-APPLY-SIGN-TO-PP-LISTS
     (17255 66
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (15047 22 (:DEFINITION TRUE-LISTP))
     (9035 50 (:DEFINITION RP::RP-TERM-LISTP))
     (8691 168
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (7728 168 (:DEFINITION QUOTEP))
     (7664 76 (:DEFINITION RP::RP-TERMP))
     (7438 168
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (7166 94
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (7055 99 (:DEFINITION APPLY$-BADGEP))
     (4937 22 (:DEFINITION SUBSETP-EQUAL))
     (4876 4875 (:REWRITE DEFAULT-CDR))
     (4651 308 (:DEFINITION MEMBER-EQUAL))
     (4631 24 (:DEFINITION RP::FALIST-CONSISTENT))
     (3597 22
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3056 3053 (:REWRITE DEFAULT-CAR))
     (2943 154
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1020 288 (:REWRITE O-P-O-INFP-CAR))
     (919 263 (:REWRITE RP::IS-IF-RP-TERMP))
     (682 682 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (637 44 (:DEFINITION NATP))
     (557 557
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (462 462
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (460 151 (:REWRITE RP::RP-TERMP-CADR))
     (402 402
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (326 326 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (308 308
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (253 99 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (250 44 (:REWRITE RP::RP-TERMP-CADDDR))
     (244 244 (:REWRITE O-P-DEF-O-FINP-1))
     (223 68 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (217 68 (:REWRITE RP::RP-TERMP-CADDR))
     (198 198
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (197 66
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (184 184 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (176 44
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (168 168 (:TYPE-PRESCRIPTION QUOTEP))
     (165 66
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (132 132 (:TYPE-PRESCRIPTION LEN))
     (132 22 (:DEFINITION ALL-NILS))
     (120 24
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (110 110 (:TYPE-PRESCRIPTION ALL-NILS))
     (110 44
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (88 88 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (66 66
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (66 66
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (48 48
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (44 44 (:LINEAR LEN-WHEN-PREFIXP))
     (24 24
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (22 22 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-<-1)))
(RP::PP-TERM-TO-PP-LISTS (398 388 (:REWRITE RP::MEASURE-LEMMA1))
                         (382 132 (:REWRITE RP::MEASURE-LEMMA1-2))
                         (197 129 (:REWRITE DEFAULT-CDR))
                         (120 40 (:REWRITE RP::CONS-COUNT-ATOM))
                         (104 4 (:REWRITE O<=-O-FINP-DEF))
                         (40 10 (:REWRITE O-P-O-INFP-CAR))
                         (40 8 (:REWRITE RP::MEASURE-LEMMA7-2))
                         (20 20 (:REWRITE RP::EX-FROM-RP-X2))
                         (20 20 (:REWRITE DEFAULT-CAR))
                         (18 18
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                         (12 4 (:REWRITE AC-<))
                         (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                         (10 10
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                         (8 4 (:REWRITE O-INFP-O-FINP-O<=))
                         (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
                         (4 2 (:REWRITE DEFAULT-<-2))
                         (4 2 (:REWRITE DEFAULT-<-1))
                         (2 2
                            (:REWRITE RP::EQUALITY-MEASURE-LEMMA1)))
(RP::PP-LISTS-P-OF-PP-TERM-TO-PP-LISTS
     (591150 2418
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (528258 806 (:DEFINITION TRUE-LISTP))
     (305766 1612 (:DEFINITION RP::RP-TERM-LISTP))
     (288858 5642
             (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (263866 5642 (:DEFINITION QUOTEP))
     (261992 5642
             (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (261192 2418 (:DEFINITION RP::RP-TERMP))
     (246110 3224
             (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (243674 3446 (:DEFINITION APPLY$-BADGEP))
     (173228 806 (:DEFINITION SUBSETP-EQUAL))
     (166872 806 (:DEFINITION RP::FALIST-CONSISTENT))
     (162750 11284 (:DEFINITION MEMBER-EQUAL))
     (129796 806
             (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (102562 5642
             (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (37274 10511 (:REWRITE O-P-O-INFP-CAR))
     (25792 7254 (:REWRITE RP::IS-IF-RP-TERMP))
     (24986 24986 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (19626 1612 (:DEFINITION NATP))
     (17732 17732
            (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (16926 16926
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (13702 13702
            (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (11646 11646
            (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (11284 11284
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (10478 3224 (:REWRITE RP::RP-TERMP-CADR))
     (8965 8899 (:REWRITE O-P-DEF-O-FINP-1))
     (8510 3446 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (8060 1612 (:REWRITE RP::RP-TERMP-CADDDR))
     (7254 7254
           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (7254 2418 (:REWRITE RP::RP-TERMP-CADDR))
     (7254 2418 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (6448 6448 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (5888 2418
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (5654 1612
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (5642 5642 (:TYPE-PRESCRIPTION QUOTEP))
     (4854 2418
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (4836 4836 (:TYPE-PRESCRIPTION LEN))
     (4836 806 (:DEFINITION ALL-NILS))
     (4030 4030 (:TYPE-PRESCRIPTION ALL-NILS))
     (4030 806
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3236 1612
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (3224 3224 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2418 2418
           (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (2418 2418
           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1612 1612 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1612 1612
           (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (1612 1612 (:LINEAR LEN-WHEN-PREFIXP))
     (902 902
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (806 806
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (806 806 (:REWRITE DEFAULT-<-2))
     (806 806 (:REWRITE DEFAULT-<-1))
     (204 204
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (66 66 (:TYPE-PRESCRIPTION O-FINP)))
(RP::PP-TERM-TO-PP-LISTS
     (52685 51
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (51353 17 (:DEFINITION TRUE-LISTP))
     (46649 34 (:DEFINITION RP::RP-TERM-LISTP))
     (46296 119
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (45767 119 (:DEFINITION QUOTEP))
     (45387 68
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (45336 68 (:DEFINITION APPLY$-BADGEP))
     (43841 17 (:DEFINITION SUBSETP-EQUAL))
     (43620 238 (:DEFINITION MEMBER-EQUAL))
     (40480 352
            (:DEFINITION RP::PP-TERM-TO-PP-LISTS))
     (28956 119
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (24387 24387 (:REWRITE DEFAULT-CDR))
     (15490 15490 (:REWRITE DEFAULT-CAR))
     (5539 119
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (5524 51 (:DEFINITION RP::RP-TERMP))
     (3529 17 (:DEFINITION RP::FALIST-CONSISTENT))
     (2747 17
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1780 1780
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (782 221 (:REWRITE O-P-O-INFP-CAR))
     (544 153 (:REWRITE RP::IS-IF-RP-TERMP))
     (527 527 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (414 34 (:DEFINITION NATP))
     (374 374
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (357 357
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (289 289
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (255 255 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (238 238
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (221 68 (:REWRITE RP::RP-TERMP-CADR))
     (187 187 (:REWRITE O-P-DEF-O-FINP-1))
     (172 68 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (170 34 (:REWRITE RP::RP-TERMP-CADDDR))
     (153 153
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (153 51 (:REWRITE RP::RP-TERMP-CADDR))
     (153 51 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (136 136 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (123 51
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (119 119 (:TYPE-PRESCRIPTION QUOTEP))
     (119 34
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (102 51
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (102 17 (:DEFINITION ALL-NILS))
     (85 85 (:TYPE-PRESCRIPTION ALL-NILS))
     (85 17
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (68 68 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (68 34
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (51 51
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (51 51
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (34 34 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (34 34
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (34 34 (:LINEAR LEN-WHEN-PREFIXP))
     (17 17
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (17 17 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE DEFAULT-<-1)))
(RP::PP-LISTS-TO-TERM-PP-LST
     (3310 12
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (2726 4 (:DEFINITION TRUE-LISTP))
     (1702 32
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1598 8 (:DEFINITION RP::RP-TERM-LISTP))
     (1572 16 (:DEFINITION RP::RP-TERMP))
     (1362 32
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1344 32 (:DEFINITION QUOTEP))
     (1248 16
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1236 16 (:DEFINITION APPLY$-BADGEP))
     (947 943 (:REWRITE DEFAULT-CDR))
     (888 4 (:DEFINITION SUBSETP-EQUAL))
     (872 8 (:DEFINITION RP::FALIST-CONSISTENT))
     (836 56 (:DEFINITION MEMBER-EQUAL))
     (644 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (606 598 (:REWRITE DEFAULT-CAR))
     (528 28
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (334 66 (:REWRITE RP::IS-IF-RP-TERMP))
     (224 42 (:REWRITE RP::RP-TERMP-CADR))
     (217 61 (:REWRITE O-P-O-INFP-CAR))
     (124 124 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (122 122
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (96 8 (:DEFINITION NATP))
     (84 84
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (76 76
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (62 16 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (60 60 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (56 56
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (52 52 (:REWRITE O-P-DEF-O-FINP-1))
     (52 8 (:REWRITE RP::RP-TERMP-CADDDR))
     (50 16 (:REWRITE RP::RP-TERMP-CADDR))
     (40 16 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (40 8
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (36 36
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (36 36 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (32 32 (:TYPE-PRESCRIPTION QUOTEP))
     (28 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (28 8
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (24 24 (:TYPE-PRESCRIPTION LEN))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (24 4 (:DEFINITION ALL-NILS))
     (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
     (16 16 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (16 8
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (12 12
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(RP::PP-FLATTEN)
(RP::SORT-SUM-META-AUX
     (10242 9 (:DEFINITION RP::SORT-SUM-META-AUX))
     (9792 9792 (:REWRITE DEFAULT-CDR))
     (8741 5
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (8379 63 (:DEFINITION RP::RP-TERMP))
     (8293 29 (:DEFINITION RP::RP-TERM-LISTP))
     (4283 29 (:DEFINITION RP::FALIST-CONSISTENT))
     (4108 4108 (:REWRITE DEFAULT-CAR))
     (3809 983 (:REWRITE O-P-O-INFP-CAR))
     (3059 19
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (2656 130
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2151 130
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2083 223 (:REWRITE RP::IS-IF-RP-TERMP))
     (1207 86 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (1163 5 (:REWRITE O<=-O-FINP-DEF))
     (1138 362 (:REWRITE DEFAULT-+-2))
     (1115 86 (:REWRITE RP::RP-TERMP-CADDR))
     (1009 137 (:REWRITE RP::RP-TERMP-CADR))
     (942 942 (:REWRITE O-P-DEF-O-FINP-1))
     (848 8 (:LINEAR ACL2-COUNT-OF-SUM))
     (588 362 (:REWRITE DEFAULT-+-1))
     (360 360
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (354 111 (:DEFINITION QUOTEP))
     (315 57
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (285 57
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (283 91 (:DEFINITION APPLY$-BADGEP))
     (211 211
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (192 91 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (171 171
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (144 36 (:DEFINITION INTEGER-ABS))
     (137 137 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (111 111 (:TYPE-PRESCRIPTION QUOTEP))
     (100 18
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (91 91 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (80 16
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (74 4
         (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
     (72 18 (:DEFINITION LENGTH))
     (67 41 (:REWRITE DEFAULT-<-2))
     (64 64 (:LINEAR LEN-WHEN-PREFIXP))
     (58 58
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (57 57
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (51 41 (:REWRITE DEFAULT-<-1))
     (41 5 (:REWRITE AC-<))
     (36 36 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
     (36 18
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (18 18
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (18 18 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (18 18
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (18 18
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 18
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (18 18 (:REWRITE DEFAULT-REALPART))
     (18 18 (:REWRITE DEFAULT-NUMERATOR))
     (18 18 (:REWRITE DEFAULT-IMAGPART))
     (18 18 (:REWRITE DEFAULT-DENOMINATOR))
     (15 15
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (15 5 (:REWRITE O-INFP-O-FINP-O<=))
     (10 10
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (8 8
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
     (5 5
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (5 5
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1)))
(RP::PP-LISTS-P-OF-SORT-SUM-META-AUX
     (118794 51
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (113992 246 (:DEFINITION RP::RP-TERM-LISTP))
     (77999 929
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (66038 737 (:DEFINITION QUOTEP))
     (65448 65448 (:REWRITE DEFAULT-CDR))
     (64774 198
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (64423 199 (:DEFINITION APPLY$-BADGEP))
     (63153 9 (:DEFINITION SUBSETP-EQUAL))
     (63036 126 (:DEFINITION MEMBER-EQUAL))
     (51582 507 (:DEFINITION RP::RP-TERMP))
     (41958 63
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (27522 7041 (:REWRITE O-P-O-INFP-CAR))
     (25927 25927 (:REWRITE DEFAULT-CAR))
     (22977 143 (:DEFINITION RP::FALIST-CONSISTENT))
     (18171 929
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (17227 107
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (16844 1823 (:REWRITE RP::IS-IF-RP-TERMP))
     (15361 613 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (11009 1192 (:REWRITE RP::RP-TERMP-CADR))
     (6827 6827 (:REWRITE O-P-DEF-O-FINP-1))
     (6125 613 (:REWRITE RP::RP-TERMP-CADDR))
     (3096 3096
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1539 277
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1473 1473
           (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (963 963
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (737 737 (:TYPE-PRESCRIPTION QUOTEP))
     (704 704 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (426 426
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (416 199 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (295 295 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (279 279 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (277 277
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (217 18 (:DEFINITION NATP))
     (189 189
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (126 126
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (90 18 (:REWRITE RP::RP-TERMP-CADDDR))
     (64 27
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (63 18
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (54 54 (:TYPE-PRESCRIPTION LEN))
     (54 27
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (54 9 (:DEFINITION ALL-NILS))
     (51 51
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (45 45 (:TYPE-PRESCRIPTION ALL-NILS))
     (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (36 18
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (27 27
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (9 9 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1)))
(RP::SORT-SUM-META (4 4 (:REWRITE DEFAULT-CDR))
                   (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (2 2 (:REWRITE DEFAULT-CAR)))
(RP::DONT-RW-SYNTAXP-OF-SORT-SUM-META.DONT-RW)
(RP::FLOOR-LEN-IS-LESS-THAN-LEN
     (703 703
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (703 703
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (703 703
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (703 703
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (368 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (281 33
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (281 33
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (272 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (165 33 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (165 33
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (165 33
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (165 33
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (165 33
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (56 8
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (35 35 (:REWRITE DEFAULT-TIMES-2))
     (35 35 (:REWRITE DEFAULT-TIMES-1))
     (33 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (30 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (30 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (27 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (23 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (22 14 (:REWRITE DEFAULT-PLUS-2))
     (21 13 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 14 (:REWRITE DEFAULT-PLUS-1))
     (13 13 (:REWRITE THE-FLOOR-BELOW))
     (13 13 (:REWRITE THE-FLOOR-ABOVE))
     (13 13 (:REWRITE DEFAULT-LESS-THAN-1))
     (10 2 (:REWRITE DEFAULT-MINUS))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE O-INFP->NEQ-0))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE DEFAULT-FLOOR-1))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(RP::NATP-LEN)
(RP::DUMMY-ARITH-LEMMA-1
     (2 2 (:LINEAR LEN-WHEN-PREFIXP))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RP::DUMMY-ARITH-LEMMA-2
     (33 3 (:REWRITE ACL2-NUMBERP-X))
     (20 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (18 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 9 (:REWRITE SIMPLIFY-SUMS-<))
     (17 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (15 3 (:REWRITE RATIONALP-X))
     (14 14 (:LINEAR LEN-WHEN-PREFIXP))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< c (- x))|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) c)|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (8 5 (:REWRITE DEFAULT-PLUS-2))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 3
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (3 3 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RP::RP-TERM-LISTP-CUT-LIST-BY-HALF
     (614 2 (:DEFINITION RP::RP-TERMP))
     (399 26
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (348 25 (:DEFINITION QUOTEP))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (277 2
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (275 1 (:DEFINITION APPLY$-BADGEP))
     (226 226 (:REWRITE DEFAULT-CAR))
     (177 1 (:DEFINITION SUBSETP-EQUAL))
     (164 14 (:DEFINITION MEMBER-EQUAL))
     (103 26
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (102 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (96 26 (:REWRITE O-P-O-INFP-CAR))
     (58 58
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (44 44 (:TYPE-PRESCRIPTION O-P))
     (40 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (31 31 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (31 18 (:REWRITE DEFAULT-<-1))
     (26 22 (:REWRITE O-P-DEF-O-FINP-1))
     (25 25 (:TYPE-PRESCRIPTION QUOTEP))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (21 18 (:REWRITE DEFAULT-<-2))
     (20 20 (:REWRITE DEFAULT-+-2))
     (20 20 (:REWRITE DEFAULT-+-1))
     (20 5 (:REWRITE RP::RP-TERMP-CADR))
     (20 4 (:REWRITE RP::RP-TERMP-CADDR))
     (20 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (20 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (20 2
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (19 2 (:DEFINITION NATP))
     (18 12 (:REWRITE ZP-OPEN))
     (18 6 (:REWRITE FOLD-CONSTS-IN-+))
     (18 1 (:DEFINITION TRUE-LISTP))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (14 14 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:TYPE-PRESCRIPTION O-FINP))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 2
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::RP-TERM-LIST-LISTP-CUT-LIST-BY-HALF
     (208 29
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (145 29
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (116 29 (:REWRITE O-P-O-INFP-CAR))
     (95 95 (:REWRITE DEFAULT-CAR))
     (87 29 (:DEFINITION QUOTEP))
     (72 72 (:REWRITE DEFAULT-CDR))
     (65 65
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (58 58 (:TYPE-PRESCRIPTION O-P))
     (29 29 (:TYPE-PRESCRIPTION QUOTEP))
     (29 29 (:REWRITE O-P-DEF-O-FINP-1))
     (29 29 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (28 7 (:REWRITE RP::RP-TERMP-CADR))
     (28 7 (:REWRITE RP::IS-IF-RP-TERMP))
     (24 12 (:REWRITE DEFAULT-<-1))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (15 12 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-+-2))
     (13 13 (:REWRITE DEFAULT-+-1))
     (12 12 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (12 4 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE ZP-OPEN))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::RP-TERM-LIST-LISTP-CUT-LIST-BY-HALF-2
     (6331 110
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (6180 50 (:DEFINITION QUOTEP))
     (6000 40
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (5960 20 (:DEFINITION APPLY$-BADGEP))
     (3900 20 (:DEFINITION SUBSETP-EQUAL))
     (3640 280 (:DEFINITION MEMBER-EQUAL))
     (2311 2044 (:REWRITE DEFAULT-CDR))
     (2280 140
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1071 1061 (:REWRITE DEFAULT-CAR))
     (620 620 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (510 153 (:REWRITE O-P-O-INFP-CAR))
     (429 110
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (420 420
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (400 40
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (380 40 (:DEFINITION NATP))
     (360 20 (:DEFINITION TRUE-LISTP))
     (280 280
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (238 238 (:TYPE-PRESCRIPTION O-P))
     (200 200 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (160 20 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (140 140
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (120 60
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (120 60
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (120 20 (:DEFINITION ALL-NILS))
     (119 119 (:REWRITE O-P-DEF-O-FINP-1))
     (100 100 (:TYPE-PRESCRIPTION ALL-NILS))
     (100 20 (:REWRITE RP::RP-TERMP-CADR))
     (100 20 (:REWRITE RP::IS-IF-RP-TERMP))
     (90 90 (:TYPE-PRESCRIPTION QUOTEP))
     (80 80 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (80 80 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (80 80 (:LINEAR LEN-WHEN-PREFIXP))
     (61 43 (:REWRITE DEFAULT-<-1))
     (60 60
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (50 50 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (46 43 (:REWRITE DEFAULT-<-2))
     (40 40
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (40 20
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (40 20
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (38 38 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (24 24 (:REWRITE DEFAULT-+-2))
     (24 24 (:REWRITE DEFAULT-+-1))
     (24 8 (:REWRITE FOLD-CONSTS-IN-+))
     (21 15 (:REWRITE ZP-OPEN))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::RP-TERM-LISTP-MERGE-SORTED-AND$-LISTS
     (2587 17 (:DEFINITION RP::RP-TERMP))
     (2349 82
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2167 69 (:DEFINITION QUOTEP))
     (1964 19
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1940 12 (:DEFINITION APPLY$-BADGEP))
     (1939 82
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1839 9 (:DEFINITION RP::FALIST-CONSISTENT))
     (1602 1598 (:REWRITE DEFAULT-CDR))
     (1428 9
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1239 7 (:DEFINITION SUBSETP-EQUAL))
     (1148 98 (:DEFINITION MEMBER-EQUAL))
     (977 973 (:REWRITE DEFAULT-CAR))
     (714 49
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (390 111 (:REWRITE O-P-O-INFP-CAR))
     (217 217 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (150 48 (:REWRITE RP::IS-IF-RP-TERMP))
     (147 147
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (141 141
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (140 14
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (133 14 (:DEFINITION NATP))
     (126 7 (:DEFINITION TRUE-LISTP))
     (98 98
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (96 30 (:REWRITE RP::RP-TERMP-CADR))
     (94 94 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (93 93 (:REWRITE O-P-DEF-O-FINP-1))
     (80 80 (:TYPE-PRESCRIPTION QUOTEP))
     (75 75 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (66 33
         (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS))
     (61 61 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (60 12
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (57 57
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (54 18 (:REWRITE RP::RP-TERMP-CADDR))
     (54 18 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (54 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (42 42 (:TYPE-PRESCRIPTION LEN))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (42 7 (:DEFINITION ALL-NILS))
     (38 12 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (35 35 (:TYPE-PRESCRIPTION ALL-NILS))
     (34 9 (:REWRITE <<-TRICHOTOMY))
     (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (26 26 (:TYPE-PRESCRIPTION <<))
     (21 21
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 3 (:REWRITE RP::NOT-INCLUDE-RP))
     (15 15
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (14 14 (:LINEAR LEN-WHEN-PREFIXP))
     (14 7
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (14 7
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (12 3 (:DEFINITION RP::INCLUDE-FNC))
     (9 9 (:REWRITE <<-TRANSITIVE))
     (8 4 (:REWRITE <<-ASYMMETRIC))
     (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::RP-TERM-LISTP-SORT-AND$-LIST
     (4281 16 (:DEFINITION RP::RP-TERMP))
     (2853 16 (:DEFINITION RP::FALIST-CONSISTENT))
     (2192 15
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1691 1691 (:REWRITE DEFAULT-CDR))
     (1180 1180 (:REWRITE DEFAULT-CAR))
     (1119 51
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (832 51
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (696 55 (:DEFINITION QUOTEP))
     (634 179 (:REWRITE O-P-O-INFP-CAR))
     (559 5
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (553 3 (:DEFINITION APPLY$-BADGEP))
     (521 75 (:REWRITE RP::IS-IF-RP-TERMP))
     (407 45 (:REWRITE RP::RP-TERMP-CADR))
     (354 2 (:DEFINITION SUBSETP-EQUAL))
     (328 28 (:DEFINITION MEMBER-EQUAL))
     (222 222
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (204 14
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (153 151 (:REWRITE O-P-DEF-O-FINP-1))
     (137 28
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (132 30 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (126 11 (:REWRITE <<-IMPLIES-LEXORDER))
     (120 30 (:REWRITE RP::RP-TERMP-CADDR))
     (99 99 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (82 21 (:REWRITE <<-TRICHOTOMY))
     (62 62 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (62 62 (:TYPE-PRESCRIPTION <<))
     (54 54
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (54 9 (:REWRITE RP::NOT-INCLUDE-RP))
     (50 50 (:TYPE-PRESCRIPTION QUOTEP))
     (42 42
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (40 4
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (38 4 (:DEFINITION NATP))
     (36 9 (:DEFINITION RP::INCLUDE-FNC))
     (36 2 (:DEFINITION TRUE-LISTP))
     (28 28
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (28 28
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (27 27 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (21 21 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (21 21 (:REWRITE <<-TRANSITIVE))
     (20 10 (:REWRITE <<-ASYMMETRIC))
     (12 7 (:REWRITE DEFAULT-<-2))
     (12 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (12 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (12 2 (:DEFINITION ALL-NILS))
     (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
     (10 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (9 9 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (7 7 (:REWRITE DEFAULT-<-1))
     (6 6 (:TYPE-PRESCRIPTION FLOOR))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 3 (:REWRITE DEFAULT-+-2))
     (4 4
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (4 2
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (4 2
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (3 3 (:REWRITE DEFAULT-+-1))
     (2 2 (:TYPE-PRESCRIPTION O-FINP))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::RP-TERM-LIST-LISTP-MERGE-SORTED-PP-LISTS
     (9162 161
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (8908 81 (:DEFINITION QUOTEP))
     (8624 56
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (8568 28 (:DEFINITION APPLY$-BADGEP))
     (5736 28 (:DEFINITION SUBSETP-EQUAL))
     (5372 392 (:DEFINITION MEMBER-EQUAL))
     (3372 196
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1708 161
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1523 452 (:REWRITE O-P-O-INFP-CAR))
     (1087 4 (:DEFINITION RP::RP-TERMP))
     (868 868 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (828 4 (:DEFINITION RP::FALIST-CONSISTENT))
     (644 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (588 588
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (560 56
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (532 56 (:DEFINITION NATP))
     (504 28 (:DEFINITION TRUE-LISTP))
     (392 392
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (357 357 (:REWRITE O-P-DEF-O-FINP-1))
     (280 280 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (220 220
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (200 28 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (168 168 (:TYPE-PRESCRIPTION LEN))
     (168 84
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (168 84
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (168 44 (:REWRITE RP::IS-IF-RP-TERMP))
     (168 28 (:DEFINITION ALL-NILS))
     (152 36 (:REWRITE RP::RP-TERMP-CADR))
     (140 140 (:TYPE-PRESCRIPTION ALL-NILS))
     (137 137 (:TYPE-PRESCRIPTION QUOTEP))
     (112 112 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (97 97 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (84 84
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (56 56
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (56 56 (:LINEAR LEN-WHEN-PREFIXP))
     (56 28
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (56 28
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (36 36
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (28 28 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (28 28 (:REWRITE DEFAULT-<-2))
     (28 28 (:REWRITE DEFAULT-<-1))
     (20 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 8 (:REWRITE RP::RP-TERMP-CADDR))
     (16 8 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::RP-TERM-LIST-LISTP-SORT-PP-LISTS
     (12197 207
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (11903 85 (:DEFINITION QUOTEP))
     (11616 84
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (11524 46 (:DEFINITION APPLY$-BADGEP))
     (7572 38 (:DEFINITION SUBSETP-EQUAL))
     (7078 532 (:DEFINITION MEMBER-EQUAL))
     (4440 266
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1463 383 (:REWRITE O-P-O-INFP-CAR))
     (1178 1178 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (798 798
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (763 207
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (760 76
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (722 76 (:DEFINITION NATP))
     (684 38 (:DEFINITION TRUE-LISTP))
     (532 532
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (484 298 (:REWRITE O-P-DEF-O-FINP-1))
     (388 388 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (372 46 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (338 68 (:REWRITE RP::IS-IF-RP-TERMP))
     (305 68 (:REWRITE RP::RP-TERMP-CADR))
     (273 273
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (228 114
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (228 114
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (228 38 (:DEFINITION ALL-NILS))
     (190 190 (:TYPE-PRESCRIPTION ALL-NILS))
     (186 186 (:TYPE-PRESCRIPTION O-FINP))
     (161 161 (:TYPE-PRESCRIPTION QUOTEP))
     (152 152 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (152 152 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (148 148 (:LINEAR LEN-WHEN-PREFIXP))
     (114 114
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (112 112
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (85 85 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (76 76
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (76 38
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (76 38
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (54 46 (:REWRITE DEFAULT-<-2))
     (50 25 (:REWRITE DEFAULT-+-2))
     (46 46 (:REWRITE DEFAULT-<-1))
     (25 25 (:REWRITE DEFAULT-+-1))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::RP-TERM-LIST-LISTP-AND$-PP-LISTS-AUX
     (1282 20 (:DEFINITION RP::RP-TERM-LISTP))
     (1021 29
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (969 20 (:DEFINITION QUOTEP))
     (897 6
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (891 3 (:DEFINITION APPLY$-BADGEP))
     (585 3 (:DEFINITION SUBSETP-EQUAL))
     (546 42 (:DEFINITION MEMBER-EQUAL))
     (407 338 (:REWRITE DEFAULT-CDR))
     (342 21
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (222 206 (:REWRITE DEFAULT-CAR))
     (147 42 (:REWRITE O-P-O-INFP-CAR))
     (122 29
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (93 93 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (70 70 (:TYPE-PRESCRIPTION O-P))
     (63 63
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (60 6
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (57 6 (:DEFINITION NATP))
     (54 3 (:DEFINITION TRUE-LISTP))
     (42 42
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (41 41
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (35 35 (:REWRITE O-P-DEF-O-FINP-1))
     (30 30 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (26 26 (:TYPE-PRESCRIPTION QUOTEP))
     (24 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (20 20 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (18 18 (:TYPE-PRESCRIPTION LEN))
     (18 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (18 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (18 3 (:DEFINITION ALL-NILS))
     (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
     (15 3 (:REWRITE RP::RP-TERMP-CADR))
     (15 3 (:REWRITE RP::IS-IF-RP-TERMP))
     (13 13 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (11 11
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (2 1
        (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS)))
(RP::RP-TERM-LIST-LISTP-AND$-PP-LISTS
     (1292 19 (:DEFINITION RP::RP-TERM-LISTP))
     (1020 28
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (970 19 (:DEFINITION QUOTEP))
     (897 6
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (891 3 (:DEFINITION APPLY$-BADGEP))
     (585 3 (:DEFINITION SUBSETP-EQUAL))
     (546 42 (:DEFINITION MEMBER-EQUAL))
     (431 345 (:REWRITE DEFAULT-CDR))
     (342 21
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (214 209 (:REWRITE DEFAULT-CAR))
     (175 49 (:REWRITE O-P-O-INFP-CAR))
     (122 28
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (93 93 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (84 84 (:TYPE-PRESCRIPTION O-P))
     (63 63
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (60 6
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (57 6 (:DEFINITION NATP))
     (54 3 (:DEFINITION TRUE-LISTP))
     (44 44
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (42 42 (:REWRITE O-P-DEF-O-FINP-1))
     (42 42
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (30 30 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (25 25 (:TYPE-PRESCRIPTION QUOTEP))
     (24 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (19 19 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (18 18 (:TYPE-PRESCRIPTION LEN))
     (18 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (18 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (18 3 (:DEFINITION ALL-NILS))
     (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
     (15 3 (:REWRITE RP::RP-TERMP-CADR))
     (15 3 (:REWRITE RP::IS-IF-RP-TERMP))
     (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8
        (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (6 6
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (4 2
        (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERM-LIST-LISTP-PP-TERM-TO-PP-LISTS
     (67962 229 (:DEFINITION RP::RP-TERMP))
     (44947 229 (:DEFINITION RP::FALIST-CONSISTENT))
     (35322 229
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (32396 32036 (:REWRITE DEFAULT-CDR))
     (21164 21164 (:REWRITE DEFAULT-CAR))
     (10218 2898 (:REWRITE O-P-O-INFP-CAR))
     (6397 961 (:REWRITE RP::IS-IF-RP-TERMP))
     (2582 468 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (2440 2440 (:REWRITE O-P-DEF-O-FINP-1))
     (2395 293
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2069 458
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1578 1578
           (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (1522 1522
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1326 221 (:REWRITE RP::NOT-INCLUDE-RP))
     (1205 1205 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1172 293
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (884 221 (:DEFINITION RP::INCLUDE-FNC))
     (550 30
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (540 30 (:DEFINITION APPLY$-BADGEP))
     (458 458
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (370 370
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (293 293
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (240 20 (:DEFINITION NATP))
     (221 221
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (148 37
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (144 144 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (120 120 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (80 30 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (74 74
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (70 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (70 20
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (60 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (36 36
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (30 30
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERMP-OF-PP-LISTS-TO-TERM-PP-LST
     (1532 57
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1422 34 (:DEFINITION QUOTEP))
     (1304 15
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1284 10 (:DEFINITION APPLY$-BADGEP))
     (1064 794 (:REWRITE DEFAULT-CDR))
     (780 4 (:DEFINITION SUBSETP-EQUAL))
     (728 56 (:DEFINITION MEMBER-EQUAL))
     (619 563 (:REWRITE DEFAULT-CAR))
     (522 162 (:REWRITE O-P-O-INFP-CAR))
     (456 28
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (240 240 (:TYPE-PRESCRIPTION O-P))
     (206 57
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (124 124 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (120 120 (:REWRITE O-P-DEF-O-FINP-1))
     (95 10 (:DEFINITION NATP))
     (92 20 (:REWRITE RP::IS-IF-RP-TERMP))
     (90 90
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (90 9
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (84 84
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (76 16 (:REWRITE RP::RP-TERMP-CADR))
     (73 5 (:DEFINITION TRUE-LISTP))
     (70 10 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (56 56
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (53 53 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (41 41 (:TYPE-PRESCRIPTION QUOTEP))
     (40 40 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (26 13
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (24 24 (:TYPE-PRESCRIPTION LEN))
     (24 4 (:DEFINITION ALL-NILS))
     (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (16 16 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (15 15
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (10 5
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (10 5
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (9 9
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-PP-FLATTEN
     (3426 211
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2526 500 (:REWRITE RP::IS-IF-RP-TERMP))
     (1506 33
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1488 395 (:REWRITE O-P-O-INFP-CAR))
     (1450 28 (:DEFINITION APPLY$-BADGEP))
     (1062 211
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (903 107
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (885 5 (:DEFINITION SUBSETP-EQUAL))
     (820 70 (:DEFINITION MEMBER-EQUAL))
     (791 195 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (767 767
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (552 69 (:DEFINITION STRIP-CDRS))
     (510 35
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (411 33 (:DEFINITION RP::RP-TERM-LIST-LISTP))
     (399 347 (:REWRITE O-P-DEF-O-FINP-1))
     (226 27 (:REWRITE RP::NOT-INCLUDE-RP))
     (172 27 (:DEFINITION RP::INCLUDE-FNC))
     (171 171 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (155 155 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (107 107
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (105 105
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (100 10
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (95 10 (:DEFINITION NATP))
     (90 5 (:DEFINITION TRUE-LISTP))
     (88 22 (:REWRITE RP::RP-TERMP-CADDDR))
     (73 73 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (72 28 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (70 70
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (68 68 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (60 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (40 10 (:REWRITE <<-TRICHOTOMY))
     (36 36 (:TYPE-PRESCRIPTION O-FINP))
     (30 30 (:TYPE-PRESCRIPTION LEN))
     (30 30 (:TYPE-PRESCRIPTION <<))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (30 5 (:DEFINITION ALL-NILS))
     (27 27 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
     (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (15 15
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (10 10 (:REWRITE <<-TRANSITIVE))
     (10 10 (:LINEAR LEN-WHEN-PREFIXP))
     (10 5
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (10 5 (:REWRITE <<-ASYMMETRIC))
     (10 5
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (5 5 (:REWRITE LEXORDER-TRANSITIVE))
     (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::RP-TERM-LIST-LISTP-STRIP-CDRS-SORT-SUM-META-AUX
     (7085 7085
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1602 267 (:REWRITE RP::NOT-INCLUDE-RP))
     (1068 267 (:DEFINITION RP::INCLUDE-FNC))
     (981 981
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (802 802 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (267 267
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC)))
(RP::RP-TERMP-OF-SORT-SUM-META.RESULT
     (597 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (462 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (339 330 (:REWRITE DEFAULT-CDR))
     (255 250 (:REWRITE DEFAULT-CAR))
     (138 39 (:REWRITE O-P-O-INFP-CAR))
     (83 23 (:REWRITE RP::IS-IF-RP-TERMP))
     (53 17 (:REWRITE RP::RP-TERMP-CADR))
     (45 5
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (44 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (40 40
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (37 6
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (33 33 (:REWRITE O-P-DEF-O-FINP-1))
     (32 6 (:REWRITE RP::RP-TERMP-CADDR))
     (24 5
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (18 3 (:REWRITE RP::NOT-INCLUDE-RP))
     (16 8 (:DEFINITION QUOTEP))
     (16 2 (:DEFINITION STRIP-CDRS))
     (15 15 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (12 3 (:DEFINITION RP::INCLUDE-FNC))
     (6 6
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5 (:TYPE-PRESCRIPTION QUOTEP))
     (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (3 3
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::VALID-SC-SUBTERMS-LST)
(RP::VALID-SC-SUBTERMS-CUT-LIST-BY-HALF
     (2070 3 (:DEFINITION RP::VALID-SC))
     (1796 66
           (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (1733 76 (:DEFINITION RP::INCLUDE-FNC))
     (813 3
          (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (801 3 (:DEFINITION RP::RP-TERMP))
     (621 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (507 507
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (483 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (468 109 (:REWRITE O-P-O-INFP-CAR))
     (402 3 (:DEFINITION RP::EVAL-AND-ALL))
     (252 6 (:DEFINITION RP::RP-TRANS))
     (206 206 (:TYPE-PRESCRIPTION O-P))
     (185 88 (:DEFINITION QUOTEP))
     (153 103 (:REWRITE O-P-DEF-O-FINP-1))
     (108 6 (:DEFINITION RP::TRANS-LIST))
     (102 6
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (84 6 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (72 6 (:DEFINITION RP::IS-SYNP$INLINE))
     (62 35 (:REWRITE DEFAULT-<-1))
     (57 57 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (54 54
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (53 35 (:REWRITE DEFAULT-<-2))
     (52 52 (:LINEAR LEN-WHEN-PREFIXP))
     (50 50 (:TYPE-PRESCRIPTION O-FINP))
     (48 6 (:DEFINITION RP::IS-FALIST))
     (45 3 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (38 38 (:REWRITE DEFAULT-+-2))
     (38 38 (:REWRITE DEFAULT-+-1))
     (36 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (33 3 (:REWRITE RP::NOT-INCLUDE-RP))
     (33 3 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (30 10 (:REWRITE FOLD-CONSTS-IN-+))
     (28 22 (:REWRITE ZP-OPEN))
     (27 27
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (27 27 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (24 24 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (24 12 (:REWRITE RP::IS-IF-RP-TERMP))
     (21 21
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (21 21 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (21 9
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (18 6 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (15 3 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (15 3
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (13 10 (:REWRITE RP::VALID-SC-CADR))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (12 6 (:REWRITE RP::RP-TERMP-CADR))
     (12 6 (:REWRITE RP::RP-TERMP-CADDR))
     (12 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (12 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 6 (:REWRITE RP::VALID-SC-CADDR))
     (6 6
        (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (6 6 (:TYPE-PRESCRIPTION QUOTEP))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (6 6 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (6 6
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (6 6
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE RP::DUMMY-ARITH-LEMMA-2))
     (6 6
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (6 3 (:REWRITE RP::VALID-SC-CADDDR))
     (6 3
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3 3 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (3 3 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::VALID-SC-SUBTERMS-LST-CUT-LIST-BY-HALF
     (812 58
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (638 58
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (435 29
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (348 348
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (348 87 (:REWRITE O-P-O-INFP-CAR))
     (348 29 (:DEFINITION RP::INCLUDE-FNC))
     (261 261
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (182 182 (:REWRITE DEFAULT-CAR))
     (174 174 (:TYPE-PRESCRIPTION O-P))
     (159 159 (:REWRITE DEFAULT-CDR))
     (87 87 (:REWRITE O-P-DEF-O-FINP-1))
     (58 29 (:DEFINITION QUOTEP))
     (24 12 (:REWRITE DEFAULT-<-1))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (15 12 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-+-2))
     (13 13 (:REWRITE DEFAULT-+-1))
     (12 12 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (12 4 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE ZP-OPEN))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::VALID-SC-SUBTERMS-LST-CUT-LIST-BY-HALF-2
     (1309 100
           (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (1011 99
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (810 50
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (780 195 (:REWRITE O-P-O-INFP-CAR))
     (660 393 (:REWRITE DEFAULT-CDR))
     (660 50 (:DEFINITION RP::INCLUDE-FNC))
     (595 595
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (447 447
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (390 390 (:TYPE-PRESCRIPTION O-P))
     (380 370 (:REWRITE DEFAULT-CAR))
     (195 195 (:REWRITE O-P-DEF-O-FINP-1))
     (130 50 (:DEFINITION QUOTEP))
     (100 20 (:REWRITE RP::VALID-SC-CADR))
     (41 23 (:REWRITE DEFAULT-<-1))
     (40 40 (:LINEAR LEN-WHEN-PREFIXP))
     (26 23 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-+-2))
     (24 24 (:REWRITE DEFAULT-+-1))
     (24 8 (:REWRITE FOLD-CONSTS-IN-+))
     (21 15 (:REWRITE ZP-OPEN))
     (18 18 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::VALID-SC-SUBTERMS-MERGE-SORTED-AND$-LISTS
     (2064 3 (:DEFINITION RP::VALID-SC))
     (1803 82 (:DEFINITION RP::INCLUDE-FNC))
     (813 3
          (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (801 3 (:DEFINITION RP::RP-TERMP))
     (721 695 (:REWRITE DEFAULT-CDR))
     (684 640 (:REWRITE DEFAULT-CAR))
     (621 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (483 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (452 110 (:REWRITE O-P-O-INFP-CAR))
     (402 3 (:DEFINITION RP::EVAL-AND-ALL))
     (252 6 (:DEFINITION RP::RP-TRANS))
     (213 94 (:DEFINITION QUOTEP))
     (166 83
          (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS))
     (134 104 (:REWRITE O-P-DEF-O-FINP-1))
     (108 6 (:DEFINITION RP::TRANS-LIST))
     (102 6
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (101 21 (:REWRITE RP::VALID-SC-CADR))
     (84 6 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (83 83 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (72 6 (:DEFINITION RP::IS-SYNP$INLINE))
     (54 54
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (54 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (48 6 (:DEFINITION RP::IS-FALIST))
     (45 3 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (36 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (34 9 (:REWRITE <<-TRICHOTOMY))
     (33 3 (:REWRITE RP::NOT-INCLUDE-RP))
     (33 3 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (30 30 (:TYPE-PRESCRIPTION O-FINP))
     (27 27
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (26 26 (:TYPE-PRESCRIPTION <<))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (24 24 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (24 12 (:REWRITE RP::IS-IF-RP-TERMP))
     (21 21
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (21 21 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (21 9
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (18 6 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (15 3 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (15 3
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (12 6 (:REWRITE RP::RP-TERMP-CADR))
     (12 6 (:REWRITE RP::RP-TERMP-CADDR))
     (12 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (12 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 9 (:REWRITE <<-TRANSITIVE))
     (9 6 (:REWRITE RP::VALID-SC-CADDR))
     (8 4 (:REWRITE <<-ASYMMETRIC))
     (6 6
        (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (6 6 (:TYPE-PRESCRIPTION QUOTEP))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (6 6 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (6 6
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (6 6
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (6 3 (:REWRITE RP::VALID-SC-CADDDR))
     (6 3
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3 3 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (3 3 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::VALID-SC-SUBTERMS-SORT-AND$-LIST
     (5080 7 (:DEFINITION RP::VALID-SC))
     (3409 104 (:DEFINITION RP::INCLUDE-FNC))
     (2151 7
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (2109 11 (:DEFINITION RP::RP-TERMP))
     (1493 11 (:DEFINITION RP::FALIST-CONSISTENT))
     (1127 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (938 7 (:DEFINITION RP::EVAL-AND-ALL))
     (798 185 (:REWRITE O-P-O-INFP-CAR))
     (588 14 (:DEFINITION RP::RP-TRANS))
     (293 136 (:DEFINITION QUOTEP))
     (271 171 (:REWRITE O-P-DEF-O-FINP-1))
     (252 14 (:DEFINITION RP::TRANS-LIST))
     (238 14
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (196 14 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (190 38 (:REWRITE RP::IS-IF-RP-TERMP))
     (168 14 (:DEFINITION RP::IS-SYNP$INLINE))
     (158 20 (:REWRITE RP::RP-TERMP-CADR))
     (126 126
          (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (112 14 (:DEFINITION RP::IS-FALIST))
     (107 7 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (100 100 (:TYPE-PRESCRIPTION O-FINP))
     (90 8 (:REWRITE <<-IMPLIES-LEXORDER))
     (84 14
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (77 29
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (77 7 (:REWRITE RP::NOT-INCLUDE-RP))
     (77 7 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (64 64
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (63 63
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (63 63
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (58 15 (:REWRITE <<-TRICHOTOMY))
     (56 56 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (55 11
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (53 53 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (48 48 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (44 44 (:TYPE-PRESCRIPTION <<))
     (42 14 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (41 32 (:REWRITE RP::VALID-SC-CADR))
     (37 7 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (36 18 (:REWRITE RP::RP-TERMP-CADDR))
     (36 18 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (29 29
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (28 28
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (28 28
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (28 7
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (22 22
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (22 11
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (21 14 (:REWRITE RP::VALID-SC-CADDR))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (18 18 (:TYPE-PRESCRIPTION QUOTEP))
     (16 8 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE <<-TRANSITIVE))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (14 14 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (14 14
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (14 14
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (14 14
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (14 14 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (14 7 (:REWRITE RP::VALID-SC-CADDDR))
     (14 7 (:REWRITE <<-ASYMMETRIC))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 4 (:REWRITE DEFAULT-+-2))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (4 4 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::VALID-SC-SUBTERMS-LST-MERGE-SORTED-PP-LISTS
     (1693 448 (:REWRITE O-P-O-INFP-CAR))
     (1608 156
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (1287 79
           (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (1050 79 (:DEFINITION RP::INCLUDE-FNC))
     (705 705
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (415 415 (:REWRITE O-P-DEF-O-FINP-1))
     (209 79 (:DEFINITION QUOTEP))
     (122 28 (:REWRITE RP::VALID-SC-CADR)))
(RP::VALID-SC-SUBTERMS-LST-SORT-PP-LISTS
     (1840 425 (:REWRITE O-P-O-INFP-CAR))
     (1685 173
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (1384 88
           (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (1120 88 (:DEFINITION RP::INCLUDE-FNC))
     (783 783
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (593 411 (:REWRITE O-P-DEF-O-FINP-1))
     (265 49 (:REWRITE RP::VALID-SC-CADR))
     (208 88 (:DEFINITION QUOTEP))
     (182 182 (:TYPE-PRESCRIPTION O-FINP))
     (75 75 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (74 74 (:LINEAR LEN-WHEN-PREFIXP))
     (52 26 (:REWRITE DEFAULT-+-2))
     (26 26 (:REWRITE DEFAULT-+-1))
     (16 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::VALID-SC-SUBTERMS-LST-AND$-PP-LISTS-AUX
     (707 20 (:DEFINITION RP::VALID-SC-SUBTERMS))
     (528 40
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (408 40
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (324 20
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (264 20 (:DEFINITION RP::INCLUDE-FNC))
     (263 68 (:REWRITE O-P-O-INFP-CAR))
     (240 240
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (197 128 (:REWRITE DEFAULT-CDR))
     (180 180
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (156 140 (:REWRITE DEFAULT-CAR))
     (130 130 (:TYPE-PRESCRIPTION O-P))
     (65 65 (:REWRITE O-P-DEF-O-FINP-1))
     (52 20 (:DEFINITION QUOTEP))
     (20 20 (:TYPE-PRESCRIPTION RP::VALID-SC))
     (15 3 (:REWRITE RP::VALID-SC-CADR))
     (11 11
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (2 1
        (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(RP::VALID-SC-SUBTERMS-LST-AND$-PP-LISTS
     (700 19 (:DEFINITION RP::VALID-SC-SUBTERMS))
     (520 38
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (406 38
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (317 19
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (303 78 (:REWRITE O-P-O-INFP-CAR))
     (260 19 (:DEFINITION RP::INCLUDE-FNC))
     (228 228
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (218 132 (:REWRITE DEFAULT-CDR))
     (171 171
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (150 150 (:TYPE-PRESCRIPTION O-P))
     (145 140 (:REWRITE DEFAULT-CAR))
     (75 75 (:REWRITE O-P-DEF-O-FINP-1))
     (54 19 (:DEFINITION QUOTEP))
     (19 19 (:TYPE-PRESCRIPTION RP::VALID-SC))
     (15 3 (:REWRITE RP::VALID-SC-CADR))
     (8 8
        (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (4 2
        (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX)))
(RP::VALID-SC-SUBTERMS-LST-PP-TERM-TO-PP-LISTS
     (143336 221 (:DEFINITION RP::VALID-SC))
     (77158 2520 (:DEFINITION RP::INCLUDE-FNC))
     (73085 1688
            (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (49140 182
            (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (48594 182 (:DEFINITION RP::RP-TERMP))
     (43848 42036 (:REWRITE DEFAULT-CDR))
     (37674 182 (:DEFINITION RP::FALIST-CONSISTENT))
     (35310 263 (:DEFINITION RP::EVAL-AND-ALL))
     (31420 28516 (:REWRITE DEFAULT-CAR))
     (29302 182
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (20286 484 (:DEFINITION RP::RP-TRANS))
     (17382 4066 (:REWRITE O-P-O-INFP-CAR))
     (8982 8982
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (8712 484 (:DEFINITION RP::TRANS-LIST))
     (8228 484
           (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (7513 3359 (:DEFINITION QUOTEP))
     (6776 484 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (5912 3702 (:REWRITE O-P-DEF-O-FINP-1))
     (5808 484 (:DEFINITION RP::IS-SYNP$INLINE))
     (5125 420
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (4356 4356
           (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (3872 484 (:DEFINITION RP::IS-FALIST))
     (2904 484
           (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (2436 223
           (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (2431 221 (:REWRITE RP::NOT-INCLUDE-RP))
     (2397 17 (:REWRITE RP::VALID-SC-EX-FROM-RP-2))
     (2210 2210 (:TYPE-PRESCRIPTION O-FINP))
     (1936 1936 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (1855 1855
           (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (1638 1638
           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (1456 728 (:REWRITE RP::IS-IF-RP-TERMP))
     (1452 484 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (1433 1433 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1394 666
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1092 1092
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1069 1069
           (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (980 196
          (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (968 968
          (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (910 182
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (788 197
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (728 364 (:REWRITE RP::RP-TERMP-CADR))
     (728 364 (:REWRITE RP::RP-TERMP-CADDR))
     (728 364 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (666 666
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (484 484
          (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (484 484 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (484 484
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (484 484
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (484 484
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (484 484 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (379 379 (:TYPE-PRESCRIPTION QUOTEP))
     (370 370
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (364 364
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (364 182
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (331 331
          (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (221 221
          (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (192 192 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (84 84
         (:TYPE-PRESCRIPTION RP::VALID-SC-SUBTERMS))
     (36 36
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS)))
(RP::VALID-SC-PP-LISTS-TO-TERM-P+
     (1722 91 (:DEFINITION RP::INCLUDE-FNC))
     (1437 869 (:REWRITE DEFAULT-CDR))
     (982 259 (:REWRITE O-P-O-INFP-CAR))
     (878 786 (:REWRITE DEFAULT-CAR))
     (482 482 (:TYPE-PRESCRIPTION O-P))
     (378 2 (:DEFINITION RP::EVAL-AND-ALL))
     (320 9 (:REWRITE RP::NOT-INCLUDE-RP))
     (250 97 (:DEFINITION QUOTEP))
     (244 4
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (241 241 (:REWRITE O-P-DEF-O-FINP-1))
     (200 24
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (172 18 (:REWRITE RP::VALID-SC-CADR))
     (164 4 (:DEFINITION RP::RP-TRANS))
     (162 24 (:DEFINITION APPLY$-BADGEP))
     (98 2
         (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (92 2 (:DEFINITION RP::RP-TERMP))
     (72 4 (:DEFINITION RP::TRANS-LIST))
     (64 4
         (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (56 4 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (52 24 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (48 4 (:DEFINITION NATP))
     (48 4 (:DEFINITION RP::IS-SYNP$INLINE))
     (42 42 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (36 36
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (34 10
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (32 4 (:DEFINITION RP::IS-FALIST))
     (20 2 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (18 18 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (16 16 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (16 4 (:REWRITE RP::VALID-SC-CADDR))
     (14 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (14 4
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (12 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (12 4 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (12 2 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (10 10
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (10 2 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (8 8
        (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (8 4 (:REWRITE RP::IS-IF-RP-TERMP))
     (8 2
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (6 6
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (4 4 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
     (4 4 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (4 4
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (4 4
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (4 4
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (4 4 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (4 2 (:REWRITE RP::RP-TERMP-CADR))
     (4 2 (:REWRITE RP::RP-TERMP-CADDR))
     (4 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (2 2 (:TYPE-PRESCRIPTION QUOTEP))
     (2 2 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (2 2 (:REWRITE RP::VALID-SC-CADDDR))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(RP::PP-FLATTEN-RETURNS-VALID-SC
     (4732 4037 (:REWRITE DEFAULT-CAR))
     (3624 34 (:DEFINITION RP::RP-TERMP))
     (3458 18
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (3402 18 (:DEFINITION RP::EVAL-AND-ALL))
     (3390 288
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2884 286 (:DEFINITION APPLY$-BADGEP))
     (2660 44
           (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (1979 93 (:REWRITE RP::NOT-INCLUDE-RP))
     (1908 44 (:DEFINITION RP::RP-TRANS))
     (1668 410 (:REWRITE O-P-O-INFP-CAR))
     (1050 1050
           (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (864 10 (:DEFINITION RP::RP-TERM-LISTP))
     (838 34
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (798 46 (:DEFINITION RP::TRANS-LIST))
     (760 286 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (742 56 (:DEFINITION NATP))
     (708 140
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (652 652 (:TYPE-PRESCRIPTION RP::TRANS-LIST))
     (610 44 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (608 36
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (566 8 (:DEFINITION RP::FALIST-CONSISTENT))
     (538 538 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (522 44 (:DEFINITION RP::IS-SYNP$INLINE))
     (462 2 (:DEFINITION SUBSETP-EQUAL))
     (446 406 (:REWRITE O-P-DEF-O-FINP-1))
     (436 28 (:DEFINITION MEMBER-EQUAL))
     (404 44 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (322 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (320 42 (:DEFINITION RP::IS-FALIST))
     (276 14
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (251 251 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (250 80
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (250 54
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (244 74 (:REWRITE RP::IS-IF-RP-TERMP))
     (244 18 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (180 42 (:REWRITE RP::RP-TERMP-CADR))
     (178 178 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (172 18
          (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (168 84
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (152 19 (:DEFINITION STRIP-CDRS))
     (140 140
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (116 116
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (104 18
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (90 18
         (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (88 88
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (84 84
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (72 72
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (68 68
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (68 44 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (68 44
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (68 44
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (68 44
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (68 44 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (68 34
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (64 32 (:REWRITE RP::RP-TERMP-CADDR))
     (64 32 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (62 62 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (60 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (54 2
         (:DEFINITION RP::VALID-SC-SUBTERMS-LST))
     (52 52 (:TYPE-PRESCRIPTION QUOTEP))
     (44 44
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (44 44
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (44 44 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 42
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (42 26 (:REWRITE RP::VALID-SC-CADDDR))
     (40 40 (:TYPE-PRESCRIPTION O-FINP))
     (40 10 (:REWRITE <<-TRICHOTOMY))
     (32 4
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (32 2 (:DEFINITION TRUE-LISTP))
     (30 30 (:TYPE-PRESCRIPTION <<))
     (28 28
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (28 28 (:REWRITE DEFAULT-<-2))
     (28 28 (:REWRITE DEFAULT-<-1))
     (26 10 (:DEFINITION RP::RP-TRANS-LST))
     (18 18
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (18 18
         (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (12 12 (:TYPE-PRESCRIPTION LEN))
     (12 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (12 2 (:DEFINITION ALL-NILS))
     (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
     (10 10 (:REWRITE <<-TRANSITIVE))
     (10 5 (:REWRITE <<-ASYMMETRIC))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (5 5 (:REWRITE LEXORDER-TRANSITIVE))
     (4 4 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (4 4
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::SORT-SUM-META-AUX-RETURNS-VALID-SC
     (12112 12044 (:REWRITE DEFAULT-CDR))
     (6244 1561 (:REWRITE O-P-O-INFP-CAR))
     (4731 4727 (:REWRITE DEFAULT-CAR))
     (1561 1561 (:REWRITE O-P-DEF-O-FINP-1))
     (648 56
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (200 200
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (10 2
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 2 (:DEFINITION APPLY$-BADGEP))
     (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::SORT-SUM-META-RETURNS-VALID-SC
     (1341 57 (:DEFINITION RP::INCLUDE-FNC))
     (827 787 (:REWRITE DEFAULT-CDR))
     (756 4 (:DEFINITION RP::EVAL-AND-ALL))
     (643 578 (:REWRITE DEFAULT-CAR))
     (576 4
          (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (552 12 (:DEFINITION RP::RP-TERMP))
     (488 8
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (400 48
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (328 8 (:DEFINITION RP::RP-TRANS))
     (324 48 (:DEFINITION APPLY$-BADGEP))
     (314 22 (:REWRITE RP::VALID-SC-CADR))
     (308 19
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (276 4 (:DEFINITION RP::RP-TERM-LISTP))
     (240 60 (:REWRITE O-P-O-INFP-CAR))
     (218 26 (:REWRITE RP::IS-IF-RP-TERMP))
     (206 18 (:REWRITE RP::RP-TERMP-CADR))
     (189 77 (:DEFINITION QUOTEP))
     (167 8 (:REWRITE RP::NOT-INCLUDE-RP))
     (144 8 (:DEFINITION RP::TRANS-LIST))
     (128 8
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (112 8 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (104 48 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (96 8 (:DEFINITION NATP))
     (96 8 (:DEFINITION RP::IS-SYNP$INLINE))
     (84 84 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (72 72
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (70 4 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (68 20
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (64 8 (:DEFINITION RP::IS-FALIST))
     (60 60 (:REWRITE O-P-DEF-O-FINP-1))
     (44 44
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (40 8
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36 36 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (32 32 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (32 8 (:REWRITE RP::VALID-SC-CADDR))
     (28 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (28 8
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (24 8 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (24 4 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (22 4 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (20 20
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (19 19 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (16 16
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (16 8
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (16 8 (:REWRITE RP::RP-TERMP-CADDR))
     (16 8 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (16 4
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (16 2 (:DEFINITION STRIP-CDRS))
     (12 12 (:TYPE-PRESCRIPTION QUOTEP))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8
        (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (8 8
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (8 8 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (8 8
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (8 8
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (8 8
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (8 8 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (4 4 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (4 4 (:REWRITE RP::VALID-SC-CADDDR))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
