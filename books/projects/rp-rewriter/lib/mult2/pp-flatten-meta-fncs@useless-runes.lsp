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
(RP::PP-HAS-BITP-RP (17152 48 (:LINEAR ACL2-COUNT-OF-SUM))
                    (15295 43 (:DEFINITION APPLY$-BADGEP))
                    (9773 74
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                    (8876 3 (:REWRITE O<=-O-FINP-DEF))
                    (8752 64 (:DEFINITION SUBSETP-EQUAL))
                    (7472 528 (:DEFINITION MEMBER-EQUAL))
                    (5719 48
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                    (4160 352
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                    (3492 56
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                    (3056 160 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                    (2536 28 (:DEFINITION TRUE-LISTP))
                    (2225 763 (:REWRITE DEFAULT-+-2))
                    (1864 56 (:DEFINITION RP::RP-TERM-LISTP))
                    (1416 116
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                    (1347 763 (:REWRITE DEFAULT-+-1))
                    (1290 86 (:DEFINITION LENGTH))
                    (1200 1200 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                    (1195 1195
                          (:TYPE-PRESCRIPTION ACL2-COUNT-OF-CONSP-POSITIVE))
                    (1192 12 (:DEFINITION RP::RP-TERMP))
                    (1142 114 (:DEFINITION LEN))
                    (1056 1056
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                    (952 952 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                    (924 924 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                    (860 172 (:REWRITE COMMUTATIVITY-OF-+))
                    (828 4 (:DEFINITION RP::FALIST-CONSISTENT))
                    (704 704
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                    (690 56 (:DEFINITION NATP))
                    (688 172 (:DEFINITION INTEGER-ABS))
                    (644 4
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                    (472 472 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                    (448 192 (:REWRITE RP::IS-IF-RP-TERMP))
                    (420 420 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
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
                    (160 160
                         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
                    (56 56 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                    (56 56 (:LINEAR BOUNDS-POSITION-EQUAL))
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
(RP::PP-TERM-P (21601 205 (:DEFINITION RP::EX-FROM-RP))
               (19248 3810 (:REWRITE RP::MEASURE-LEMMA1))
               (18882 526 (:REWRITE RP::NOT-INCLUDE-RP))
               (18224 226 (:DEFINITION RP::INCLUDE-FNC))
               (17056 1446 (:REWRITE RP::MEASURE-LEMMA1-2))
               (14219 141 (:DEFINITION APPLY$-BADGEP))
               (13643 165
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
               (6177 36 (:DEFINITION SUBSETP-EQUAL))
               (5765 4365 (:REWRITE DEFAULT-CDR))
               (5313 270 (:DEFINITION MEMBER-EQUAL))
               (4782 18
                     (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
               (4207 9 (:DEFINITION TRUE-LISTP))
               (3528 45
                     (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
               (3456 27 (:DEFINITION RP::RP-TERMP))
               (3315 144
                     (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
               (3252 90 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
               (3233 1974 (:REWRITE DEFAULT-CAR))
               (2502 9 (:DEFINITION RP::FALIST-CONSISTENT))
               (1962 9
                     (:DEFINITION RP::FALIST-CONSISTENT-AUX))
               (1326 1326
                     (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
               (1285 271 (:DEFINITION QUOTEP))
               (1256 1256
                     (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
               (1076 18 (:DEFINITION RP::RP-TERM-LISTP))
               (1052 120
                     (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
               (939 66 (:DEFINITION NATP))
               (756 141 (:DEFINITION WEAK-APPLY$-BADGE-P))
               (700 20 (:REWRITE RP::EX-FROM-RP-X2))
               (585 585 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
               (540 540 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
               (468 468 (:REWRITE SUBSETP-IMPLIES-MEMBER))
               (453 45
                    (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
               (434 122 (:REWRITE O-P-O-INFP-CAR))
               (432 432
                    (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
               (412 412
                    (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
               (360 108 (:REWRITE RP::IS-IF-RP-TERMP))
               (288 288
                    (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
               (252 252 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
               (222 99
                    (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
               (206 81
                    (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
               (144 36 (:REWRITE RP::RP-TERMP-CADDDR))
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
               (90 90
                   (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
               (9 9 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
               (9 9 (:LINEAR BOUNDS-POSITION-EQUAL))
               (8 4 (:REWRITE O-INFP-O-FINP-O<=))
               (4 4
                  (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::CUT-LIST-BY-HALF)
(RP::TRUE-LISTP-OF-CUT-LIST-BY-HALF.FIRST
     (6123 21
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (5990 7 (:DEFINITION TRUE-LISTP))
     (4121 14 (:DEFINITION RP::RP-TERM-LISTP))
     (3932 28
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (3869 28 (:DEFINITION QUOTEP))
     (3792 14
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3778 7 (:DEFINITION APPLY$-BADGEP))
     (3106 28 (:DEFINITION SUBSETP-EQUAL))
     (2546 210 (:DEFINITION MEMBER-EQUAL))
     (1981 28
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1904 7 (:DEFINITION RP::RP-TERMP))
     (1755 1755 (:REWRITE DEFAULT-CDR))
     (1715 70 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1600 112
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1449 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (1127 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (806 806 (:REWRITE DEFAULT-CAR))
     (420 420 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (364 364 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (336 336
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (294 84 (:REWRITE O-P-O-INFP-CAR))
     (259 259 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (224 224
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (196 196 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (140 140 (:TYPE-PRESCRIPTION O-P))
     (133 14 (:DEFINITION NATP))
     (91 91
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (84 35 (:REWRITE RP::IS-IF-RP-TERMP))
     (70 70 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (70 70
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (70 70 (:REWRITE O-P-DEF-O-FINP-1))
     (63 63
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (63 63
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (56 56 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (56 21 (:REWRITE RP::RP-TERMP-CADR))
     (49 49 (:TYPE-PRESCRIPTION LEN))
     (49 7 (:DEFINITION LEN))
     (47 40 (:REWRITE DEFAULT-+-2))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (42 7 (:DEFINITION ALL-NILS))
     (40 40 (:REWRITE DEFAULT-+-1))
     (35 35 (:TYPE-PRESCRIPTION ALL-NILS))
     (35 7
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (28 28 (:TYPE-PRESCRIPTION QUOTEP))
     (28 14 (:REWRITE RP::RP-TERMP-CADDR))
     (28 14 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (28 7 (:DEFINITION WEAK-APPLY$-BADGE-P))
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
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL))
     (6 6 (:REWRITE ZP-OPEN)))
(RP::TRUE-LISTP-OF-CUT-LIST-BY-HALF.SECOND
     (29698 91
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (20641 108
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (20396 108 (:DEFINITION QUOTEP))
     (20027 38 (:DEFINITION APPLY$-BADGEP))
     (19252 50 (:DEFINITION RP::RP-TERM-LISTP))
     (17981 74
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (16390 148 (:DEFINITION SUBSETP-EQUAL))
     (13430 1110 (:DEFINITION MEMBER-EQUAL))
     (9053 370 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (8440 592
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (8431 8431 (:REWRITE DEFAULT-CDR))
     (8239 108
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (7952 29 (:DEFINITION RP::RP-TERMP))
     (6003 29 (:DEFINITION RP::FALIST-CONSISTENT))
     (4669 29
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3650 3650 (:REWRITE DEFAULT-CAR))
     (2220 2220 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2202 37
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1924 1924 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1776 1776
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1218 348 (:REWRITE O-P-O-INFP-CAR))
     (1184 1184
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1036 1036 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (728 74 (:DEFINITION NATP))
     (580 580 (:TYPE-PRESCRIPTION O-P))
     (396 157 (:REWRITE RP::IS-IF-RP-TERMP))
     (388 388 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (370 370
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (349 349
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (290 290 (:REWRITE O-P-DEF-O-FINP-1))
     (261 261
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (259 259 (:TYPE-PRESCRIPTION LEN))
     (259 37 (:DEFINITION LEN))
     (257 257
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (240 203 (:REWRITE DEFAULT-+-2))
     (232 87 (:REWRITE RP::RP-TERMP-CADR))
     (230 115
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (224 224 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (222 111
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (222 37 (:DEFINITION ALL-NILS))
     (203 203 (:REWRITE DEFAULT-+-1))
     (185 185 (:TYPE-PRESCRIPTION ALL-NILS))
     (152 38 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (145 29
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
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
     (41 41 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (41 41 (:LINEAR BOUNDS-POSITION-EQUAL))
     (37 37 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (37 37 (:REWRITE DEFAULT-<-2))
     (37 37 (:REWRITE DEFAULT-<-1))
     (32 8 (:REWRITE RP::RP-TERMP-CADDDR))
     (29 29
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (11 11 (:REWRITE ZP-OPEN)))
(RP::CUT-LIST-BY-HALF-RETURNS-PP-LISTS
     (22891 63
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (21253 21 (:DEFINITION TRUE-LISTP))
     (15457 42 (:DEFINITION RP::RP-TERM-LISTP))
     (15016 147
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (14365 147 (:DEFINITION QUOTEP))
     (13903 84
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (13840 88 (:DEFINITION APPLY$-BADGEP))
     (11526 84 (:DEFINITION SUBSETP-EQUAL))
     (9846 630 (:DEFINITION MEMBER-EQUAL))
     (6825 147
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6804 63 (:DEFINITION RP::RP-TERMP))
     (6180 336
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (6125 6125 (:REWRITE DEFAULT-CDR))
     (6111 210 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (4347 21 (:DEFINITION RP::FALIST-CONSISTENT))
     (3683 3683 (:REWRITE DEFAULT-CAR))
     (3381 21
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1554 1554 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (1260 1260 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1092 1092 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1008 1008
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (966 273 (:REWRITE O-P-O-INFP-CAR))
     (672 672
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (672 189 (:REWRITE RP::IS-IF-RP-TERMP))
     (588 588 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (508 42 (:DEFINITION NATP))
     (462 462 (:TYPE-PRESCRIPTION O-P))
     (462 462
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (357 357
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (328 328 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (273 84 (:REWRITE RP::RP-TERMP-CADR))
     (259 229 (:REWRITE DEFAULT-+-2))
     (231 231 (:REWRITE O-P-DEF-O-FINP-1))
     (229 229 (:REWRITE DEFAULT-+-1))
     (218 88 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (210 210
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (210 42 (:REWRITE RP::RP-TERMP-CADDDR))
     (200 200 (:REWRITE ZP-OPEN))
     (189 189
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (189 63 (:REWRITE RP::RP-TERMP-CADDR))
     (189 63 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (168 168 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (151 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (147 147 (:TYPE-PRESCRIPTION QUOTEP))
     (147 42
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (126 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (126 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (126 21 (:DEFINITION ALL-NILS))
     (105 105 (:TYPE-PRESCRIPTION ALL-NILS))
     (105 21
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
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
     (28 28 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (28 28 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (9 9 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (9 9 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (2 2 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (2 2 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (1 1 (:REWRITE |(* (- x) y)|))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
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
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
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
                     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::LESS-THAN-2-OF-LEN-IS
     (452 19 (:REWRITE RP::POS-LEN-IMPLIES))
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
     (8 8 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (8 8 (:LINEAR BOUNDS-POSITION-EQUAL))
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
(RP::MERGE-SORTED-AND$-LISTS (2537 5 (:REWRITE O<=-O-FINP-DEF))
                             (2150 8 (:LINEAR ACL2-COUNT-OF-SUM))
                             (1175 365 (:REWRITE DEFAULT-+-2))
                             (705 365 (:REWRITE DEFAULT-+-1))
                             (663 51 (:REWRITE RP::POS-LEN-IMPLIES))
                             (312 78 (:DEFINITION INTEGER-ABS))
                             (211 134 (:REWRITE DEFAULT-<-2))
                             (156 39 (:DEFINITION LENGTH))
                             (154 134 (:REWRITE DEFAULT-<-1))
                             (102 102 (:LINEAR LEN-WHEN-PREFIXP))
                             (91 91 (:REWRITE DEFAULT-CAR))
                             (90 90 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                             (87 5
                                 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
                             (85 85 (:REWRITE DEFAULT-CDR))
                             (78 78 (:REWRITE DEFAULT-UNARY-MINUS))
                             (78 39
                                 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                             (72 18 (:REWRITE O-P-O-INFP-CAR))
                             (51 51 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                             (51 51 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (155209 348
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (82660 203 (:DEFINITION RP::RP-TERM-LISTP))
     (80628 438
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (79551 438 (:DEFINITION QUOTEP))
     (78411 213 (:DEFINITION APPLY$-BADGEP))
     (71629 350
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (67861 138 (:DEFINITION RP::RP-TERMP))
     (67054 438
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (62726 540 (:DEFINITION SUBSETP-EQUAL))
     (53614 114 (:DEFINITION RP::FALIST-CONSISTENT))
     (48050 4050 (:DEFINITION MEMBER-EQUAL))
     (46745 4076 (:REWRITE RP::POS-LEN-IMPLIES))
     (42294 114
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (35522 1350 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (33270 31788 (:REWRITE DEFAULT-CDR))
     (30200 2160
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (15970 14216 (:REWRITE DEFAULT-CAR))
     (8100 8100 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (7156 3983 (:REWRITE DEFAULT-<-2))
     (7150 143
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (7020 7020 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (6640 6640 (:LINEAR LEN-WHEN-PREFIXP))
     (6480 6480
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (4800 1371 (:REWRITE O-P-O-INFP-CAR))
     (4320 4320
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (3983 3983
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3983 3983 (:REWRITE DEFAULT-<-1))
     (3780 3780 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (3320 3320 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3320 3320 (:LINEAR BOUNDS-POSITION-EQUAL))
     (2682 270 (:DEFINITION NATP))
     (2592 213 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (2499 1035
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (2160 2160 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (2067 117
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1779 135 (:DEFINITION ALL-NILS))
     (1674 639 (:REWRITE RP::IS-IF-RP-TERMP))
     (1370 1370
           (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (1350 1350
           (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
                    (4 4 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                    (4 4 (:LINEAR BOUNDS-POSITION-EQUAL))
                    (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                    (2 1 (:REWRITE DEFAULT-+-2))
                    (1 1 (:REWRITE DEFAULT-+-1)))
(RP::TRUE-LISTP-OF-SORT-AND$-LIST
     (113559 255
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (61509 151 (:DEFINITION RP::RP-TERM-LISTP))
     (59534 336
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (58582 336 (:DEFINITION QUOTEP))
     (57977 160 (:DEFINITION APPLY$-BADGEP))
     (50957 270
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (49176 109 (:DEFINITION RP::RP-TERMP))
     (46845 336
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (45908 392 (:DEFINITION SUBSETP-EQUAL))
     (37568 93 (:DEFINITION RP::FALIST-CONSISTENT))
     (35228 2940 (:DEFINITION MEMBER-EQUAL))
     (29315 85
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (25980 980 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (24335 22918 (:REWRITE DEFAULT-CDR))
     (22128 1568
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (12425 10258 (:REWRITE DEFAULT-CAR))
     (7188 106
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (5880 5880 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (5212 2900 (:REWRITE DEFAULT-<-2))
     (5096 5096 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (4880 4880 (:LINEAR LEN-WHEN-PREFIXP))
     (4704 4704
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (3490 969 (:REWRITE O-P-O-INFP-CAR))
     (3136 3136
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (3099 3099
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2900 2900 (:REWRITE DEFAULT-<-1))
     (2744 2744 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2440 2440 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (2440 2440 (:LINEAR BOUNDS-POSITION-EQUAL))
     (2359 160 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1990 761
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (1966 196 (:DEFINITION NATP))
     (1813 100
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1605 1605 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (1298 98 (:DEFINITION ALL-NILS))
     (1266 474 (:REWRITE RP::IS-IF-RP-TERMP))
     (1013 1013
           (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (980 980
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (68 68 (:TYPE-PRESCRIPTION FLOOR))
     (68 34 (:REWRITE DEFAULT-UNARY-MINUS))
     (68 34 (:REWRITE DEFAULT-+-2))
     (62 62 (:TYPE-PRESCRIPTION <<))
     (34 34 (:REWRITE DEFAULT-+-1))
     (21 21 (:REWRITE <<-TRANSITIVE))
     (20 10 (:REWRITE <<-ASYMMETRIC))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::SORT-AND$-LIST
     (35626 64
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (25950 54 (:DEFINITION APPLY$-BADGEP))
     (21189 27
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (21115 27 (:DEFINITION QUOTEP))
     (17684 13 (:DEFINITION RP::RP-TERM-LISTP))
     (17643 69 (:DEFINITION SUBSETP-EQUAL))
     (14776 430 (:DEFINITION MEMBER-EQUAL))
     (14010 27
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (13928 7 (:DEFINITION RP::RP-TERMP))
     (13775 107
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (13720 832
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (13125 608 (:REWRITE ACL2-NUMBERP-X))
     (11112 281 (:REWRITE RATIONALP-X))
     (9755 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (8794 225
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (8159 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (7595 160 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (6248 351
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (5567 4 (:DEFINITION RP::SORT-AND$-LIST))
     (3819 3444 (:REWRITE DEFAULT-CDR))
     (3026 40
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2199 1298 (:REWRITE DEFAULT-CAR))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1552 54 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1430 832
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1073 163
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (1053 1053
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (985 985 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (960 832 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (838 834
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (834 834
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (832 832
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (832 832 (:REWRITE |(equal c (/ x))|))
     (832 832 (:REWRITE |(equal c (- x))|))
     (832 832 (:REWRITE |(equal (/ x) c)|))
     (832 832 (:REWRITE |(equal (/ x) (/ y))|))
     (832 832 (:REWRITE |(equal (- x) c)|))
     (832 832 (:REWRITE |(equal (- x) (- y))|))
     (747 747 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (702 702
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (692 692 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (644 36 (:DEFINITION ALL-NILS))
     (608 608
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (542 147
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (531 339 (:REWRITE DEFAULT-LESS-THAN-2))
     (531 159 (:REWRITE DEFAULT-PLUS-2))
     (510 323
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (496 496 (:LINEAR LEN-WHEN-PREFIXP))
     (458 458 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (395 373 (:REWRITE REDUCE-INTEGERP-+))
     (374 4 (:REWRITE |(+ x (if a b c))|))
     (373 373 (:REWRITE INTEGERP-MINUS-X))
     (373 373
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (373 373 (:META META-INTEGERP-CORRECT))
     (367 323
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (358 358
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (341 339 (:REWRITE DEFAULT-LESS-THAN-1))
     (339 339 (:REWRITE THE-FLOOR-BELOW))
     (339 339 (:REWRITE THE-FLOOR-ABOVE))
     (336 7
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (333 333
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (333 333
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (329 325
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (325 325 (:REWRITE INTEGERP-<-CONSTANT))
     (325 325 (:REWRITE CONSTANT-<-INTEGERP))
     (325 325
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (325 325
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (325 325
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (325 325
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (325 325 (:REWRITE |(< c (- x))|))
     (325 325
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (325 325
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (325 325
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (325 325
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (325 325 (:REWRITE |(< (/ x) (/ y))|))
     (325 325 (:REWRITE |(< (- x) c)|))
     (325 325 (:REWRITE |(< (- x) (- y))|))
     (323 323 (:REWRITE SIMPLIFY-SUMS-<))
     (302 84 (:REWRITE O-P-O-INFP-CAR))
     (296 250
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (295 295 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (281 281 (:REWRITE REDUCE-RATIONALP-+))
     (281 281 (:REWRITE REDUCE-RATIONALP-*))
     (281 281 (:REWRITE RATIONALP-MINUS-X))
     (281 281
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (281 281 (:META META-RATIONALP-CORRECT))
     (264 264 (:REWRITE |(< 0 (* x y))|))
     (250 250 (:REWRITE |(< 0 (/ x))|))
     (249 249
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (248 248 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (248 248 (:LINEAR BOUNDS-POSITION-EQUAL))
     (212 4 (:REWRITE |(+ (+ x y) z)|))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (180 180 (:TYPE-PRESCRIPTION ALL-NILS))
     (175 159 (:REWRITE DEFAULT-PLUS-1))
     (160 160
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (156 4 (:REWRITE |(- (if a b c))|))
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
     (7446 15
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (6762 5 (:DEFINITION TRUE-LISTP))
     (4002 16 (:DEFINITION RP::RP-TERM-LISTP))
     (3719 47
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (3540 15 (:DEFINITION RP::RP-TERMP))
     (3432 47 (:DEFINITION QUOTEP))
     (3404 47
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3295 38 (:DEFINITION APPLY$-BADGEP))
     (3292 26
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2610 20 (:DEFINITION SUBSETP-EQUAL))
     (2401 200 (:REWRITE RP::POS-LEN-IMPLIES))
     (2370 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (2070 150 (:DEFINITION MEMBER-EQUAL))
     (1855 5
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1484 1419 (:REWRITE DEFAULT-CDR))
     (1440 50 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1300 80
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (981 896 (:REWRITE DEFAULT-CAR))
     (360 195 (:REWRITE DEFAULT-<-2))
     (340 340 (:LINEAR LEN-WHEN-PREFIXP))
     (300 300 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (260 260 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (246 69 (:REWRITE O-P-O-INFP-CAR))
     (240 240
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (195 195
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (195 195 (:REWRITE DEFAULT-<-1))
     (172 51 (:REWRITE RP::IS-IF-RP-TERMP))
     (170 170 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (170 170 (:LINEAR BOUNDS-POSITION-EQUAL))
     (170 38 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (160 160
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (141 50
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (140 140 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (127 127 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (122 122
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (121 10 (:DEFINITION NATP))
     (109 109
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (90 5
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (77 26 (:REWRITE RP::RP-TERMP-CADR))
     (65 5 (:DEFINITION ALL-NILS))
     (59 59 (:REWRITE O-P-DEF-O-FINP-1))
     (50 50
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (15 15
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (15 15
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::MERGE-SORTED-PP-LISTS (3950 5 (:REWRITE O<=-O-FINP-DEF))
                           (3520 10 (:LINEAR ACL2-COUNT-OF-SUM))
                           (1739 537 (:REWRITE DEFAULT-+-2))
                           (1183 91 (:REWRITE RP::POS-LEN-IMPLIES))
                           (1043 537 (:REWRITE DEFAULT-+-1))
                           (480 120 (:DEFINITION INTEGER-ABS))
                           (368 130 (:REWRITE DEFAULT-CDR))
                           (339 216 (:REWRITE DEFAULT-<-2))
                           (240 60 (:DEFINITION LENGTH))
                           (238 136 (:REWRITE DEFAULT-CAR))
                           (236 216 (:REWRITE DEFAULT-<-1))
                           (204 51 (:REWRITE O-P-O-INFP-CAR))
                           (182 182 (:LINEAR LEN-WHEN-PREFIXP))
                           (151 151
                                (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                           (120 120 (:REWRITE DEFAULT-UNARY-MINUS))
                           (120 60
                                (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                           (91 91 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                           (91 91 (:LINEAR BOUNDS-POSITION-EQUAL))
                           (90 5
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
     (5070 390 (:REWRITE RP::POS-LEN-IMPLIES))
     (780 780 (:LINEAR LEN-WHEN-PREFIXP))
     (780 390 (:REWRITE DEFAULT-<-2))
     (656 164 (:REWRITE O-P-O-INFP-CAR))
     (390 390
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (390 390 (:REWRITE DEFAULT-<-1))
     (390 390 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (390 390 (:LINEAR BOUNDS-POSITION-EQUAL))
     (164 164 (:REWRITE O-P-DEF-O-FINP-1))
     (124 124
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP)))
(RP::MERGE-SORTED-PP-LISTS (1209 93 (:REWRITE RP::POS-LEN-IMPLIES))
                           (396 6
                                (:DEFINITION RP::MERGE-SORTED-PP-LISTS))
                           (312 24 (:DEFINITION ACONS))
                           (288 16 (:REWRITE CONS-CAR-CDR))
                           (236 59 (:REWRITE O-P-O-INFP-CAR))
                           (186 186 (:LINEAR LEN-WHEN-PREFIXP))
                           (186 93 (:REWRITE DEFAULT-<-2))
                           (93 93 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                           (93 93 (:REWRITE DEFAULT-<-1))
                           (93 93 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                           (93 93 (:LINEAR BOUNDS-POSITION-EQUAL))
                           (59 59 (:REWRITE O-P-DEF-O-FINP-1))
                           (41 41
                               (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                           (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
                           (4 4 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::SORT-PP-LISTS (26086 4 (:DEFINITION RP::EX-FROM-RP))
                   (25160 8 (:DEFINITION APPLY$-BADGEP))
                   (23580 1836 (:REWRITE RP::MEASURE-LEMMA1))
                   (18470 1594 (:REWRITE RP::SORT-MEASURE-LEMMA2))
                   (15094 16
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (14720 46
                          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (14714 4 (:REWRITE RP::NOT-INCLUDE-RP))
                   (14702 4 (:DEFINITION RP::INCLUDE-FNC))
                   (14574 8 (:DEFINITION TRUE-LISTP))
                   (12812 40
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (12748 24 (:DEFINITION RP::RP-TERMP))
                   (11870 1352 (:REWRITE RP::MEASURE-LEMMA1-2))
                   (10784 8 (:DEFINITION RP::FALIST-CONSISTENT))
                   (10767 2325 (:REWRITE DEFAULT-CDR))
                   (10698 110
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (9211 465
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                   (8256 8
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (8042 1004 (:REWRITE DEFAULT-CAR))
                   (6862 122 (:REWRITE LEN-WHEN-PREFIXP))
                   (4632 32 (:DEFINITION SUBSETP-EQUAL))
                   (3712 120
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                   (3674 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (2864 240 (:DEFINITION MEMBER-EQUAL))
                   (2786 80 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                   (2188 120
                         (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                   (2146 16 (:DEFINITION RP::RP-TERM-LISTP))
                   (1800 128
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (1748 1748 (:LINEAR LEN-WHEN-PREFIXP))
                   (1185 465
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                   (874 874 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                   (874 874 (:LINEAR BOUNDS-POSITION-EQUAL))
                   (761 761
                        (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (751 465 (:REWRITE DEFAULT-<-2))
                   (696 696 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                   (588 465 (:REWRITE DEFAULT-<-1))
                   (480 480 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (416 416 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                   (384 384
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (350 128 (:REWRITE O-P-O-INFP-CAR))
                   (336 40
                        (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (330 8 (:DEFINITION ALL-NILS))
                   (320 96 (:REWRITE RP::IS-IF-RP-TERMP))
                   (256 256
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (236 236 (:TYPE-PRESCRIPTION PREFIXP))
                   (230 230 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (224 224 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (222 8
                        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (216 16 (:DEFINITION NATP))
                   (212 44 (:DEFINITION QUOTEP))
                   (161 161
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
                   (96 96
                       (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                   (96 96
                       (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (96 32 (:REWRITE RP::RP-TERMP-CADR))
                   (96 32 (:REWRITE RP::RP-TERMP-CADDR))
                   (96 32 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (80 80
                       (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (69304 123
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (63634 41 (:DEFINITION TRUE-LISTP))
     (40786 128 (:DEFINITION RP::RP-TERM-LISTP))
     (38531 369
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36066 369 (:DEFINITION QUOTEP))
     (34985 296 (:DEFINITION APPLY$-BADGEP))
     (34954 210
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (29390 164 (:DEFINITION SUBSETP-EQUAL))
     (29224 135 (:DEFINITION RP::RP-TERMP))
     (28012 369
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (24962 1230 (:DEFINITION MEMBER-EQUAL))
     (19434 41 (:DEFINITION RP::FALIST-CONSISTENT))
     (15570 656
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (15454 410 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (15211 41
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3714 1980 (:REWRITE DEFAULT-<-2))
     (3438 3438 (:LINEAR LEN-WHEN-PREFIXP))
     (2929 835 (:REWRITE O-P-O-INFP-CAR))
     (2460 2460 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2132 2132 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (2017 2017
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1980 1980 (:REWRITE DEFAULT-<-1))
     (1968 1968
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1719 1719 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (1719 1719 (:LINEAR BOUNDS-POSITION-EQUAL))
     (1636 517 (:REWRITE RP::IS-IF-RP-TERMP))
     (1369 296 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1312 1312
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1150 410
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (1148 1148 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1088 1088
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1063 1063 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (986 82 (:DEFINITION NATP))
     (862 616 (:REWRITE O-P-DEF-O-FINP-1))
     (859 859
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (797 312 (:REWRITE RP::RP-TERMP-CADR))
     (738 41
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (533 41 (:DEFINITION ALL-NILS))
     (470 82 (:REWRITE RP::RP-TERMP-CADDDR))
     (410 410
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (246 246 (:TYPE-PRESCRIPTION O-FINP))
     (246 123
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (205 205 (:TYPE-PRESCRIPTION ALL-NILS))
     (134 67 (:REWRITE DEFAULT-UNARY-MINUS))
     (134 67 (:REWRITE DEFAULT-+-2))
     (123 123
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (123 123
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (82 82
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (67 67 (:REWRITE DEFAULT-+-1))
     (41 41
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::SORT-PP-LISTS (6672 15
                         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (6418 5 (:DEFINITION TRUE-LISTP))
                   (3494 9 (:DEFINITION RP::RP-TERM-LISTP))
                   (3320 28
                         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (3206 28 (:DEFINITION QUOTEP))
                   (3119 20 (:DEFINITION APPLY$-BADGEP))
                   (3114 16
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (3078 28
                         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (3054 11 (:DEFINITION RP::RP-TERMP))
                   (2494 20 (:DEFINITION SUBSETP-EQUAL))
                   (2336 5 (:DEFINITION RP::FALIST-CONSISTENT))
                   (1954 150 (:DEFINITION MEMBER-EQUAL))
                   (1855 5
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (1474 1379 (:REWRITE DEFAULT-CDR))
                   (1392 50 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                   (1226 80
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (1102 751 (:REWRITE DEFAULT-CAR))
                   (366 2 (:DEFINITION RP::SORT-PP-LISTS))
                   (353 193 (:REWRITE DEFAULT-<-2))
                   (320 320 (:LINEAR LEN-WHEN-PREFIXP))
                   (300 300 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (290 290 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                   (286 79 (:REWRITE O-P-O-INFP-CAR))
                   (260 260 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                   (240 240
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (230 230
                        (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (195 193 (:REWRITE DEFAULT-<-1))
                   (160 160
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (160 160 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                   (160 160 (:LINEAR BOUNDS-POSITION-EQUAL))
                   (140 140 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (133 20 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (120 37 (:REWRITE RP::IS-IF-RP-TERMP))
                   (112 44
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (103 103 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (94 5
                       (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (85 61 (:REWRITE O-P-DEF-O-FINP-1))
                   (83 83
                       (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (72 72
                       (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                   (65 5 (:DEFINITION ALL-NILS))
                   (55 18 (:REWRITE RP::RP-TERMP-CADR))
                   (50 50
                       (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (12033 34
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (10664 11 (:DEFINITION TRUE-LISTP))
     (8304 67
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (7919 66 (:DEFINITION QUOTEP))
     (7900 20 (:DEFINITION RP::RP-TERM-LISTP))
     (7683 37 (:DEFINITION APPLY$-BADGEP))
     (7158 42
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6382 52 (:DEFINITION SUBSETP-EQUAL))
     (5342 390 (:DEFINITION MEMBER-EQUAL))
     (3459 130 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (3352 208
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3341 3249 (:REWRITE DEFAULT-CDR))
     (3294 28 (:DEFINITION RP::RP-TERMP))
     (3219 67
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2092 12 (:DEFINITION RP::FALIST-CONSISTENT))
     (1833 1833 (:REWRITE DEFAULT-CAR))
     (1610 10
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (780 780 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (676 676 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (627 21
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (624 624
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (574 160 (:REWRITE O-P-O-INFP-CAR))
     (416 416
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (403 101 (:REWRITE RP::IS-IF-RP-TERMP))
     (364 364 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (292 26 (:DEFINITION NATP))
     (222 222
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (211 52 (:REWRITE RP::RP-TERMP-CADR))
     (170 170
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (170 170 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (138 138 (:REWRITE O-P-DEF-O-FINP-1))
     (130 130
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (39 39
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (34 34
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (28 28 (:LINEAR LEN-WHEN-PREFIXP))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (14 14 (:LINEAR BOUNDS-POSITION-EQUAL))
     (13 13 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (13 13 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-<-1))
     (12 12
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (4 2
        (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS)))
(RP::PP-LISTS-P-OF-AND$-PP-LISTS-AUX
     (45064 132
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (41596 44 (:DEFINITION TRUE-LISTP))
     (29590 94 (:DEFINITION RP::RP-TERM-LISTP))
     (28816 294
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (27274 294 (:DEFINITION QUOTEP))
     (26336 162
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (26175 159 (:DEFINITION APPLY$-BADGEP))
     (21595 176 (:DEFINITION SUBSETP-EQUAL))
     (18075 1320 (:DEFINITION MEMBER-EQUAL))
     (14410 124 (:DEFINITION RP::RP-TERMP))
     (14199 294
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (12287 12285 (:REWRITE DEFAULT-CDR))
     (11698 440 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (11356 704
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (9207 48 (:DEFINITION RP::FALIST-CONSISTENT))
     (7139 44
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (6895 6891 (:REWRITE DEFAULT-CAR))
     (2640 2640 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2288 2288 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (2112 2112
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (2000 566 (:REWRITE O-P-O-INFP-CAR))
     (1526 436 (:REWRITE RP::IS-IF-RP-TERMP))
     (1408 1408
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1232 1232 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1103 88 (:DEFINITION NATP))
     (928 928
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (782 242 (:REWRITE RP::RP-TERMP-CADR))
     (740 740
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (632 632
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (592 592 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (478 478 (:REWRITE O-P-DEF-O-FINP-1))
     (440 440
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (44 44 (:REWRITE DEFAULT-<-1))
     (44 44 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (44 44 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::AND$-PP-LISTS (58208 160
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (53490 53 (:DEFINITION TRUE-LISTP))
                   (39197 108 (:DEFINITION RP::RP-TERM-LISTP))
                   (38720 360
                          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (36983 359 (:DEFINITION QUOTEP))
                   (35650 205 (:DEFINITION APPLY$-BADGEP))
                   (35277 208
                          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (29915 220 (:DEFINITION SUBSETP-EQUAL))
                   (25515 1650 (:DEFINITION MEMBER-EQUAL))
                   (17032 154 (:DEFINITION RP::RP-TERMP))
                   (16931 360
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (16516 15636 (:REWRITE DEFAULT-CDR))
                   (16016 880
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (15901 550 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                   (10831 54 (:DEFINITION RP::FALIST-CONSISTENT))
                   (9624 9423 (:REWRITE DEFAULT-CAR))
                   (8417 52
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (3483 1098 (:REWRITE O-P-O-INFP-CAR))
                   (3300 3300 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (2860 2860 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                   (2640 2640
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (1770 504 (:REWRITE RP::IS-IF-RP-TERMP))
                   (1760 1760
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (1540 1540 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (1364 110 (:DEFINITION NATP))
                   (1148 1148
                         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (920 102
                        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (888 888
                        (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
                   (807 254 (:REWRITE RP::RP-TERMP-CADR))
                   (795 795 (:REWRITE O-P-DEF-O-FINP-1))
                   (776 776 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (550 550
                        (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
                   (541 205 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (504 96 (:REWRITE RP::RP-TERMP-CADDDR))
                   (472 472
                        (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
                   (470 154 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (468 468
                        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                   (464 154 (:REWRITE RP::RP-TERMP-CADDR))
                   (422 422 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (387 152
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
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
                   (165 165
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (160 160
                        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                   (112 112 (:LINEAR LEN-WHEN-PREFIXP))
                   (108 108
                        (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                   (56 56 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                   (56 56 (:LINEAR BOUNDS-POSITION-EQUAL))
                   (55 55 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (55 55 (:REWRITE DEFAULT-<-2))
                   (55 55 (:REWRITE DEFAULT-<-1))
                   (54 54
                       (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::PP-LISTS-P-OF-AND$-PP-LISTS
     (48140 135
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (43996 45 (:DEFINITION TRUE-LISTP))
     (31612 96 (:DEFINITION RP::RP-TERM-LISTP))
     (30883 331
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (29088 331 (:DEFINITION QUOTEP))
     (28010 186
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (27830 195 (:DEFINITION APPLY$-BADGEP))
     (22971 180 (:DEFINITION SUBSETP-EQUAL))
     (19371 1350 (:DEFINITION MEMBER-EQUAL))
     (15270 147 (:DEFINITION RP::RP-TERMP))
     (14958 331
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (12956 12956 (:REWRITE DEFAULT-CDR))
     (12353 450 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (12168 720
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (9424 49 (:DEFINITION RP::FALIST-CONSISTENT))
     (7714 7714 (:REWRITE DEFAULT-CAR))
     (7310 45
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (2700 2700 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2340 2340 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (2160 2160
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (2086 589 (:REWRITE O-P-O-INFP-CAR))
     (1758 485 (:REWRITE RP::IS-IF-RP-TERMP))
     (1440 1440
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1260 1260 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1199 90 (:DEFINITION NATP))
     (1080 1080
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (845 256 (:REWRITE RP::RP-TERMP-CADR))
     (797 797
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (689 689
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (663 663 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (499 499 (:REWRITE O-P-DEF-O-FINP-1))
     (493 195 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (486 90 (:REWRITE RP::RP-TERMP-CADDDR))
     (450 450
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (135 135
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (135 135
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (118 59
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS-AUX))
     (98 98
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (90 90 (:LINEAR LEN-WHEN-PREFIXP))
     (49 49
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (45 45 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (45 45 (:REWRITE DEFAULT-<-2))
     (45 45 (:REWRITE DEFAULT-<-1))
     (45 45 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (45 45 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::APPEND-OF-PP-LIST-P
     (12466 36
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (11542 12 (:DEFINITION TRUE-LISTP))
     (8236 24 (:DEFINITION RP::RP-TERM-LISTP))
     (7996 84
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (7627 84 (:DEFINITION QUOTEP))
     (7363 48
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (7327 51 (:DEFINITION APPLY$-BADGEP))
     (6088 48 (:DEFINITION SUBSETP-EQUAL))
     (5128 360 (:DEFINITION MEMBER-EQUAL))
     (3885 84
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3876 36 (:DEFINITION RP::RP-TERMP))
     (3462 3438 (:REWRITE DEFAULT-CDR))
     (3274 120 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (3220 192
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2484 12 (:DEFINITION RP::FALIST-CONSISTENT))
     (2104 2095 (:REWRITE DEFAULT-CAR))
     (1932 12
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (720 720 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (624 624 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (576 576
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (540 153 (:REWRITE O-P-O-INFP-CAR))
     (384 384
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (372 108 (:REWRITE RP::IS-IF-RP-TERMP))
     (336 336 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (291 24 (:DEFINITION NATP))
     (258 258 (:TYPE-PRESCRIPTION O-P))
     (231 231
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (204 204
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (174 174 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (153 48 (:REWRITE RP::RP-TERMP-CADR))
     (129 129 (:REWRITE O-P-DEF-O-FINP-1))
     (126 51 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (120 120
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (12 12 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (12 12 (:LINEAR BOUNDS-POSITION-EQUAL))
     (6 6 (:REWRITE CONSP-OF-APPEND))
     (5 5 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(RP::PP-LISTS-P-IMPLIES-TRUE-LISTP
     (4793 15
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (4521 5 (:DEFINITION TRUE-LISTP))
     (3159 10 (:DEFINITION RP::RP-TERM-LISTP))
     (3042 29
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2931 29 (:DEFINITION QUOTEP))
     (2843 16
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2830 15 (:DEFINITION APPLY$-BADGEP))
     (2342 20 (:DEFINITION SUBSETP-EQUAL))
     (1942 150 (:DEFINITION MEMBER-EQUAL))
     (1541 29
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1516 11 (:DEFINITION RP::RP-TERMP))
     (1332 1332 (:REWRITE DEFAULT-CDR))
     (1279 50 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1220 80
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1035 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (805 5
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (726 726 (:REWRITE DEFAULT-CAR))
     (300 300 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (260 260 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (240 240
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (222 63 (:REWRITE O-P-O-INFP-CAR))
     (160 160
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (140 140 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (120 37 (:REWRITE RP::IS-IF-RP-TERMP))
     (111 10 (:DEFINITION NATP))
     (106 106 (:TYPE-PRESCRIPTION O-P))
     (84 84
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (77 77
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (61 61 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (55 18 (:REWRITE RP::RP-TERMP-CADR))
     (53 53 (:REWRITE O-P-DEF-O-FINP-1))
     (50 50
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (5 5 (:REWRITE DEFAULT-<-1))
     (5 5 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (5 5 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::APPLY-SIGN-TO-PP-LISTS)
(RP::PP-LISTS-P-OF-APPLY-SIGN-TO-PP-LISTS
     (24005 66
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (21797 22 (:DEFINITION TRUE-LISTP))
     (15785 50 (:DEFINITION RP::RP-TERM-LISTP))
     (15441 168
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (14478 168 (:DEFINITION QUOTEP))
     (13916 94
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (13805 99 (:DEFINITION APPLY$-BADGEP))
     (11335 88 (:DEFINITION SUBSETP-EQUAL))
     (9575 660 (:DEFINITION MEMBER-EQUAL))
     (7664 76 (:DEFINITION RP::RP-TERMP))
     (7438 168
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6412 6411 (:REWRITE DEFAULT-CDR))
     (6090 220 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (6016 352
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (4631 24 (:DEFINITION RP::FALIST-CONSISTENT))
     (3738 3735 (:REWRITE DEFAULT-CAR))
     (3597 22
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1320 1320 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1144 1144 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1056 1056
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1020 288 (:REWRITE O-P-O-INFP-CAR))
     (919 263 (:REWRITE RP::IS-IF-RP-TERMP))
     (704 704
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (637 44 (:DEFINITION NATP))
     (616 616 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (557 557
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (460 151 (:REWRITE RP::RP-TERMP-CADR))
     (402 402
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (326 326 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (253 99 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (250 44 (:REWRITE RP::RP-TERMP-CADDDR))
     (244 244 (:REWRITE O-P-DEF-O-FINP-1))
     (223 68 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (220 220
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (22 22 (:REWRITE DEFAULT-<-1))
     (22 22 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (22 22 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (831792 2418
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (768900 806 (:DEFINITION TRUE-LISTP))
     (546408 1612 (:DEFINITION RP::RP-TERM-LISTP))
     (529500 5642
             (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (504508 5642 (:DEFINITION QUOTEP))
     (486752 3224
             (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (484316 3446 (:DEFINITION APPLY$-BADGEP))
     (400974 3224 (:DEFINITION SUBSETP-EQUAL))
     (336494 24180 (:DEFINITION MEMBER-EQUAL))
     (261992 5642
             (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (261192 2418 (:DEFINITION RP::RP-TERMP))
     (216462 8060 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (211266 12896
             (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (166872 806 (:DEFINITION RP::FALIST-CONSISTENT))
     (129796 806
             (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (48360 48360 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (41912 41912 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (38688 38688
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (37472 10544 (:REWRITE O-P-O-INFP-CAR))
     (25792 25792
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (25792 7254 (:REWRITE RP::IS-IF-RP-TERMP))
     (22568 22568
            (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (19626 1612 (:DEFINITION NATP))
     (17732 17732
            (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (13702 13702
            (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (11646 11646
            (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (10478 3224 (:REWRITE RP::RP-TERMP-CADR))
     (9064 8932 (:REWRITE O-P-DEF-O-FINP-1))
     (8510 3446 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (8060 8060
           (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (2418 2418
           (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (2418 2418
           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1612 1612 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1612 1612
           (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (1612 1612 (:LINEAR LEN-WHEN-PREFIXP))
     (964 964
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (806 806
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (806 806 (:REWRITE DEFAULT-<-2))
     (806 806 (:REWRITE DEFAULT-<-1))
     (806 806 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (806 806 (:LINEAR BOUNDS-POSITION-EQUAL))
     (204 204
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (132 132 (:TYPE-PRESCRIPTION O-FINP)))
(RP::PP-TERM-TO-PP-LISTS
     (89020 51
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (87688 17 (:DEFINITION TRUE-LISTP))
     (82984 34 (:DEFINITION RP::RP-TERM-LISTP))
     (82631 119
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (82102 119 (:DEFINITION QUOTEP))
     (81722 68
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (81671 68 (:DEFINITION APPLY$-BADGEP))
     (79904 68 (:DEFINITION SUBSETP-EQUAL))
     (78544 510 (:DEFINITION MEMBER-EQUAL))
     (71070 618
            (:DEFINITION RP::PP-TERM-TO-PP-LISTS))
     (49112 272
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (40279 40279 (:REWRITE DEFAULT-CDR))
     (35825 170 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (25593 25593 (:REWRITE DEFAULT-CAR))
     (5539 119
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (5524 51 (:DEFINITION RP::RP-TERMP))
     (3529 17 (:DEFINITION RP::FALIST-CONSISTENT))
     (3110 3110
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2747 17
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1020 1020 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (884 884 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (816 816
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (782 221 (:REWRITE O-P-O-INFP-CAR))
     (544 544
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (544 153 (:REWRITE RP::IS-IF-RP-TERMP))
     (476 476 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (414 34 (:DEFINITION NATP))
     (374 374
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (289 289
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (255 255 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (221 68 (:REWRITE RP::RP-TERMP-CADR))
     (187 187 (:REWRITE O-P-DEF-O-FINP-1))
     (172 68 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (170 170
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (17 17 (:REWRITE DEFAULT-<-1))
     (17 17 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (17 17 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::PP-LISTS-TO-TERM-PP-LST
     (4526 12
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (3942 4 (:DEFINITION TRUE-LISTP))
     (2918 32
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2814 8 (:DEFINITION RP::RP-TERM-LISTP))
     (2560 32 (:DEFINITION QUOTEP))
     (2464 16
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2452 16 (:DEFINITION APPLY$-BADGEP))
     (2040 16 (:DEFINITION SUBSETP-EQUAL))
     (1720 120 (:DEFINITION MEMBER-EQUAL))
     (1572 16 (:DEFINITION RP::RP-TERMP))
     (1362 32
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1239 1235 (:REWRITE DEFAULT-CDR))
     (1096 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1080 64
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (872 8 (:DEFINITION RP::FALIST-CONSISTENT))
     (730 722 (:REWRITE DEFAULT-CAR))
     (644 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (334 66 (:REWRITE RP::IS-IF-RP-TERMP))
     (240 240 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (224 42 (:REWRITE RP::RP-TERMP-CADR))
     (217 61 (:REWRITE O-P-O-INFP-CAR))
     (208 208 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (192 192
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (128 128
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (122 122
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (96 8 (:DEFINITION NATP))
     (76 76
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (62 16 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (60 60 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (52 52 (:REWRITE O-P-DEF-O-FINP-1))
     (52 8 (:REWRITE RP::RP-TERMP-CADDDR))
     (50 16 (:REWRITE RP::RP-TERMP-CADDR))
     (40 40
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (32 32 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (32 32 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (169095 51
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (164293 246 (:DEFINITION RP::RP-TERM-LISTP))
     (128300 929
             (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (116339 737 (:DEFINITION QUOTEP))
     (115075 198
             (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (114724 199 (:DEFINITION APPLY$-BADGEP))
     (113310 36 (:DEFINITION SUBSETP-EQUAL))
     (112590 270 (:DEFINITION MEMBER-EQUAL))
     (94392 94392 (:REWRITE DEFAULT-CDR))
     (70380 144
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (51582 507 (:DEFINITION RP::RP-TERMP))
     (50031 90 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (39450 10023 (:REWRITE O-P-O-INFP-CAR))
     (33514 33514 (:REWRITE DEFAULT-CAR))
     (22977 143 (:DEFINITION RP::FALIST-CONSISTENT))
     (18171 929
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (17227 107
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (16844 1823 (:REWRITE RP::IS-IF-RP-TERMP))
     (15361 613 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (11009 1192 (:REWRITE RP::RP-TERMP-CADR))
     (9809 9809 (:REWRITE O-P-DEF-O-FINP-1))
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
     (540 540 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (468 468 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (432 432
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (426 426
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (416 199 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (295 295 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (288 288
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (277 277
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (252 252 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (217 18 (:DEFINITION NATP))
     (90 90
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (36 18
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (27 27
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (9 9 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (9 9 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (9 9 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (668 26
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (617 25 (:DEFINITION QUOTEP))
     (614 2 (:DEFINITION RP::RP-TERMP))
     (546 2
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (544 1 (:DEFINITION APPLY$-BADGEP))
     (430 4 (:DEFINITION SUBSETP-EQUAL))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (350 30 (:DEFINITION MEMBER-EQUAL))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (243 243 (:REWRITE DEFAULT-CAR))
     (239 10 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (220 16
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (103 26
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (96 26 (:REWRITE O-P-O-INFP-CAR))
     (60 60 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (58 58
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (52 52 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (48 48
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (44 44 (:TYPE-PRESCRIPTION O-P))
     (40 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (32 32
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (31 31 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (31 18 (:REWRITE DEFAULT-<-1))
     (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (26 22 (:REWRITE O-P-DEF-O-FINP-1))
     (25 25 (:TYPE-PRESCRIPTION QUOTEP))
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
     (18 18 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (18 18 (:LINEAR BOUNDS-POSITION-EQUAL))
     (18 12 (:REWRITE ZP-OPEN))
     (18 6 (:REWRITE FOLD-CONSTS-IN-+))
     (18 1 (:DEFINITION TRUE-LISTP))
     (14 14 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (10 10
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (6 3
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
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
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
     (6 6 (:REWRITE ZP-OPEN))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::RP-TERM-LIST-LISTP-CUT-LIST-BY-HALF-2
     (11991 110
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (11840 50 (:DEFINITION QUOTEP))
     (11660 40
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (11620 20 (:DEFINITION APPLY$-BADGEP))
     (9240 80 (:DEFINITION SUBSETP-EQUAL))
     (7640 600 (:DEFINITION MEMBER-EQUAL))
     (5060 200 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (4800 320
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3351 3084 (:REWRITE DEFAULT-CDR))
     (1691 1681 (:REWRITE DEFAULT-CAR))
     (1200 1200 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1040 1040 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (960 960
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (640 640
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (560 560 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (510 153 (:REWRITE O-P-O-INFP-CAR))
     (429 110
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (400 40
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (380 40 (:DEFINITION NATP))
     (360 20 (:DEFINITION TRUE-LISTP))
     (238 238 (:TYPE-PRESCRIPTION O-P))
     (200 200 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (200 200
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (80 80 (:LINEAR LEN-WHEN-PREFIXP))
     (61 43 (:REWRITE DEFAULT-<-1))
     (60 60
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (50 50 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (46 43 (:REWRITE DEFAULT-<-2))
     (40 40
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (40 40 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (40 40 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (4232 82
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (4050 69 (:DEFINITION QUOTEP))
     (3847 19
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3823 12 (:DEFINITION APPLY$-BADGEP))
     (3010 28 (:DEFINITION SUBSETP-EQUAL))
     (2587 17 (:DEFINITION RP::RP-TERMP))
     (2450 210 (:DEFINITION MEMBER-EQUAL))
     (1966 1962 (:REWRITE DEFAULT-CDR))
     (1939 82
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1839 9 (:DEFINITION RP::FALIST-CONSISTENT))
     (1673 70 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1540 112
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1428 9
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1096 1092 (:REWRITE DEFAULT-CAR))
     (420 420 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (390 111 (:REWRITE O-P-O-INFP-CAR))
     (364 364 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (336 336
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (224 224
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (196 196 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (150 48 (:REWRITE RP::IS-IF-RP-TERMP))
     (141 141
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (140 14
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (133 14 (:DEFINITION NATP))
     (126 7 (:DEFINITION TRUE-LISTP))
     (96 30 (:REWRITE RP::RP-TERMP-CADR))
     (94 94 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (93 93 (:REWRITE O-P-DEF-O-FINP-1))
     (80 80 (:TYPE-PRESCRIPTION QUOTEP))
     (75 75 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (70 70
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL))
     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(RP::RP-TERM-LISTP-SORT-AND$-LIST
     (4281 16 (:DEFINITION RP::RP-TERMP))
     (2853 16 (:DEFINITION RP::FALIST-CONSISTENT))
     (2192 15
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1795 1795 (:REWRITE DEFAULT-CDR))
     (1370 51
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1234 55 (:DEFINITION QUOTEP))
     (1214 1214 (:REWRITE DEFAULT-CAR))
     (1119 51
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1097 5
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1091 3 (:DEFINITION APPLY$-BADGEP))
     (860 8 (:DEFINITION SUBSETP-EQUAL))
     (700 60 (:DEFINITION MEMBER-EQUAL))
     (634 179 (:REWRITE O-P-O-INFP-CAR))
     (521 75 (:REWRITE RP::IS-IF-RP-TERMP))
     (478 20 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (440 32
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (407 45 (:REWRITE RP::RP-TERMP-CADR))
     (222 222
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (153 151 (:REWRITE O-P-DEF-O-FINP-1))
     (137 28
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (132 30 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (126 11 (:REWRITE <<-IMPLIES-LEXORDER))
     (120 120 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (120 30 (:REWRITE RP::RP-TERMP-CADDR))
     (104 104 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (99 99 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (82 21 (:REWRITE <<-TRICHOTOMY))
     (64 64
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (62 62 (:TYPE-PRESCRIPTION <<))
     (56 56 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (54 54
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (54 9 (:REWRITE RP::NOT-INCLUDE-RP))
     (50 50 (:TYPE-PRESCRIPTION QUOTEP))
     (40 4
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (38 4 (:DEFINITION NATP))
     (36 9 (:DEFINITION RP::INCLUDE-FNC))
     (36 2 (:DEFINITION TRUE-LISTP))
     (28 28
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (27 27 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (21 21 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (21 21 (:REWRITE <<-TRANSITIVE))
     (20 20
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (20 10 (:REWRITE <<-ASYMMETRIC))
     (12 12 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (12 12 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (17330 161
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (17076 81 (:DEFINITION QUOTEP))
     (16792 56
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (16736 28 (:DEFINITION APPLY$-BADGEP))
     (13456 112 (:DEFINITION SUBSETP-EQUAL))
     (11216 840 (:DEFINITION MEMBER-EQUAL))
     (7328 280 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (7036 448
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1711 508 (:REWRITE O-P-O-INFP-CAR))
     (1708 161
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1680 1680 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1456 1456 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1344 1344
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1087 4 (:DEFINITION RP::RP-TERMP))
     (896 896
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (828 4 (:DEFINITION RP::FALIST-CONSISTENT))
     (784 784 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (644 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (560 56
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (532 56 (:DEFINITION NATP))
     (504 28 (:DEFINITION TRUE-LISTP))
     (401 401 (:REWRITE O-P-DEF-O-FINP-1))
     (280 280 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (280 280
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (28 28 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (28 28 (:LINEAR BOUNDS-POSITION-EQUAL))
     (20 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 8 (:REWRITE RP::RP-TERMP-CADDR))
     (16 8 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::RP-TERM-LIST-LISTP-SORT-PP-LISTS
     (23077 207
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (22783 85 (:DEFINITION QUOTEP))
     (22496 84
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (22404 46 (:DEFINITION APPLY$-BADGEP))
     (17844 152 (:DEFINITION SUBSETP-EQUAL))
     (14804 1140 (:DEFINITION MEMBER-EQUAL))
     (9740 380 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (9300 608
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2280 2280 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1976 1976 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1824 1824
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1463 383 (:REWRITE O-P-O-INFP-CAR))
     (1216 1216
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1064 1064 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (763 207
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (760 76
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (722 76 (:DEFINITION NATP))
     (684 38 (:DEFINITION TRUE-LISTP))
     (484 298 (:REWRITE O-P-DEF-O-FINP-1))
     (388 388 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (380 380
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (74 74 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (74 74 (:LINEAR BOUNDS-POSITION-EQUAL))
     (54 46 (:REWRITE DEFAULT-<-2))
     (50 25 (:REWRITE DEFAULT-+-2))
     (46 46 (:REWRITE DEFAULT-<-1))
     (25 25 (:REWRITE DEFAULT-+-1))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::RP-TERM-LIST-LISTP-AND$-PP-LISTS-AUX
     (2131 20 (:DEFINITION RP::RP-TERM-LISTP))
     (1870 29
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1818 20 (:DEFINITION QUOTEP))
     (1746 6
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1740 3 (:DEFINITION APPLY$-BADGEP))
     (1386 12 (:DEFINITION SUBSETP-EQUAL))
     (1146 90 (:DEFINITION MEMBER-EQUAL))
     (759 30 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (720 48
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (563 494 (:REWRITE DEFAULT-CDR))
     (315 299 (:REWRITE DEFAULT-CAR))
     (180 180 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (156 156 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (147 42 (:REWRITE O-P-O-INFP-CAR))
     (144 144
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (122 29
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (84 84 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (70 70 (:TYPE-PRESCRIPTION O-P))
     (60 6
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (57 6 (:DEFINITION NATP))
     (54 3 (:DEFINITION TRUE-LISTP))
     (41 41
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (35 35 (:REWRITE O-P-DEF-O-FINP-1))
     (30 30 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (30 30
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
     (2 1
        (:TYPE-PRESCRIPTION RP::TRUE-LISTP-OF-MERGE-SORTED-AND$-LISTS)))
(RP::RP-TERM-LIST-LISTP-AND$-PP-LISTS
     (2141 19 (:DEFINITION RP::RP-TERM-LISTP))
     (1869 28
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1819 19 (:DEFINITION QUOTEP))
     (1746 6
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1740 3 (:DEFINITION APPLY$-BADGEP))
     (1386 12 (:DEFINITION SUBSETP-EQUAL))
     (1146 90 (:DEFINITION MEMBER-EQUAL))
     (759 30 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (720 48
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (587 501 (:REWRITE DEFAULT-CDR))
     (307 302 (:REWRITE DEFAULT-CAR))
     (180 180 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (175 49 (:REWRITE O-P-O-INFP-CAR))
     (156 156 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (144 144
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (122 28
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (84 84 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (84 84 (:TYPE-PRESCRIPTION O-P))
     (60 6
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (57 6 (:DEFINITION NATP))
     (54 3 (:DEFINITION TRUE-LISTP))
     (44 44
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (42 42 (:REWRITE O-P-DEF-O-FINP-1))
     (30 30 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (30 30
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3 3 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (2664 57
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2554 34 (:DEFINITION QUOTEP))
     (2436 15
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2416 10 (:DEFINITION APPLY$-BADGEP))
     (1848 16 (:DEFINITION SUBSETP-EQUAL))
     (1528 120 (:DEFINITION MEMBER-EQUAL))
     (1272 1002 (:REWRITE DEFAULT-CDR))
     (1012 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (960 64
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (743 687 (:REWRITE DEFAULT-CAR))
     (522 162 (:REWRITE O-P-O-INFP-CAR))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (240 240 (:TYPE-PRESCRIPTION O-P))
     (240 240 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (208 208 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (206 57
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (192 192
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (128 128
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (120 120 (:REWRITE O-P-DEF-O-FINP-1))
     (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (95 10 (:DEFINITION NATP))
     (92 20 (:REWRITE RP::IS-IF-RP-TERMP))
     (90 90
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (90 9
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (76 16 (:REWRITE RP::RP-TERMP-CADR))
     (73 5 (:DEFINITION TRUE-LISTP))
     (70 10 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (53 53 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (41 41 (:TYPE-PRESCRIPTION QUOTEP))
     (40 40
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-PP-FLATTEN
     (4771 211
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2851 33
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2795 28 (:DEFINITION APPLY$-BADGEP))
     (2526 500 (:REWRITE RP::IS-IF-RP-TERMP))
     (2150 20 (:DEFINITION SUBSETP-EQUAL))
     (1750 150 (:DEFINITION MEMBER-EQUAL))
     (1488 395 (:REWRITE O-P-O-INFP-CAR))
     (1195 50 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1100 80
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1062 211
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (903 107
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (791 195 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (767 767
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (552 69 (:DEFINITION STRIP-CDRS))
     (411 33 (:DEFINITION RP::RP-TERM-LIST-LISTP))
     (399 347 (:REWRITE O-P-DEF-O-FINP-1))
     (300 300 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (260 260 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (240 240
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (226 27 (:REWRITE RP::NOT-INCLUDE-RP))
     (172 27 (:DEFINITION RP::INCLUDE-FNC))
     (171 171 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (160 160
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (140 140 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (107 107
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (100 10
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (95 10 (:DEFINITION NATP))
     (90 5 (:DEFINITION TRUE-LISTP))
     (88 22 (:REWRITE RP::RP-TERMP-CADDDR))
     (73 73 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (72 28 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (68 68 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (60 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (50 50
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (5 5 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (5 5 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (26 26 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (26 26 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (20 20 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (20 20 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (37 37 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (37 37 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (4794 4099 (:REWRITE DEFAULT-CAR))
     (4246 34 (:DEFINITION RP::RP-TERMP))
     (4080 18
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (4012 288
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3506 286 (:DEFINITION APPLY$-BADGEP))
     (3402 18 (:DEFINITION RP::EVAL-AND-ALL))
     (2660 44
           (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (1979 93 (:REWRITE RP::NOT-INCLUDE-RP))
     (1908 44 (:DEFINITION RP::RP-TRANS))
     (1668 410 (:REWRITE O-P-O-INFP-CAR))
     (1486 10 (:DEFINITION RP::RP-TERM-LISTP))
     (1460 34
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1052 8 (:DEFINITION SUBSETP-EQUAL))
     (1050 1050
           (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (892 60 (:DEFINITION MEMBER-EQUAL))
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
     (562 20 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (560 32
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (538 538 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (522 44 (:DEFINITION RP::IS-SYNP$INLINE))
     (446 406 (:REWRITE O-P-DEF-O-FINP-1))
     (404 44 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (322 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (320 42 (:DEFINITION RP::IS-FALIST))
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
     (120 120 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (116 116
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (104 104 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (104 18
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
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
     (64 64
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (64 32 (:REWRITE RP::RP-TERMP-CADDR))
     (64 32 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (60 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (56 56 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (54 2
         (:DEFINITION RP::VALID-SC-SUBTERMS-LST))
     (52 52 (:TYPE-PRESCRIPTION QUOTEP))
     (44 44
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (44 44
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (44 44 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 26 (:REWRITE RP::VALID-SC-CADDDR))
     (40 40 (:TYPE-PRESCRIPTION O-FINP))
     (40 10 (:REWRITE <<-TRICHOTOMY))
     (32 4
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (32 2 (:DEFINITION TRUE-LISTP))
     (30 30 (:TYPE-PRESCRIPTION <<))
     (28 28 (:REWRITE DEFAULT-<-2))
     (28 28 (:REWRITE DEFAULT-<-1))
     (26 10 (:DEFINITION RP::RP-TRANS-LST))
     (20 20
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (5 5 (:REWRITE LEXORDER-TRANSITIVE))
     (4 4 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (4 4
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (2 2 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
