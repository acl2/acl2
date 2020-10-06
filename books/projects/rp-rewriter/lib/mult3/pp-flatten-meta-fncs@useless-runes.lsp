(RP::AND-LIST-HASH-AUX
     (9348 246
           (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (8396 2249 (:REWRITE DEFAULT-+-2))
     (4586 2249 (:REWRITE DEFAULT-+-1))
     (3444 246 (:DEFINITION EXPT))
     (3409 949 (:REWRITE DEFAULT-*-2))
     (3030 2950 (:REWRITE DEFAULT-CDR))
     (2728 637 (:REWRITE DEFAULT-UNARY-MINUS))
     (2671 949 (:REWRITE DEFAULT-*-1))
     (2091 123 (:REWRITE DEFAULT-UNARY-/))
     (1907 1124 (:REWRITE DEFAULT-<-1))
     (1616 1124 (:REWRITE DEFAULT-<-2))
     (1413 1393 (:REWRITE DEFAULT-CAR))
     (1174 294 (:REWRITE O-P-O-INFP-CAR))
     (908 908
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (645 129
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (492 246 (:REWRITE ZIP-OPEN))
     (387 129 (:DEFINITION APPLY$-BADGEP))
     (369 123 (:REWRITE DEFAULT-NUMERATOR))
     (369 123 (:REWRITE DEFAULT-DENOMINATOR))
     (304 288 (:REWRITE O-P-DEF-O-FINP-1))
     (274 137
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (258 258 (:REWRITE FOLD-CONSTS-IN-+))
     (258 129 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (246 246 (:REWRITE O-INFP->NEQ-0))
     (137 137
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (137 137
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (136 136 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (129 129 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (16 16 (:TYPE-PRESCRIPTION O-FINP)))
(RP::INTEGERP-OF-AND-LIST-HASH-AUX.HASH
     (1204 86 (:DEFINITION EXPT))
     (642 522 (:REWRITE DEFAULT-CDR))
     (527 381 (:REWRITE DEFAULT-+-2))
     (446 228 (:REWRITE DEFAULT-*-2))
     (430 381 (:REWRITE DEFAULT-+-1))
     (352 22
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (293 263 (:REWRITE DEFAULT-CAR))
     (278 228 (:REWRITE DEFAULT-*-1))
     (268 61 (:REWRITE O-P-O-INFP-CAR))
     (182 179 (:REWRITE DEFAULT-<-1))
     (179 179 (:REWRITE DEFAULT-<-2))
     (172 86 (:REWRITE ZIP-OPEN))
     (167 167
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (103 70 (:REWRITE DEFAULT-UNARY-MINUS))
     (86 86 (:REWRITE O-INFP->NEQ-0))
     (85 61 (:REWRITE O-P-DEF-O-FINP-1))
     (55 11
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (33 11 (:DEFINITION APPLY$-BADGEP))
     (24 24 (:TYPE-PRESCRIPTION O-FINP))
     (22 11 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (14 14 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (11 11 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (11 11 (:REWRITE DEFAULT-UNARY-/))
     (11 11 (:REWRITE DEFAULT-NUMERATOR))
     (11 11 (:REWRITE DEFAULT-DENOMINATOR))
     (4 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::NATP-OF-AND-LIST-HASH-AUX.REST-SIZE
     (56 4 (:DEFINITION EXPT))
     (44 44 (:REWRITE DEFAULT-CDR))
     (34 22 (:REWRITE DEFAULT-<-1))
     (22 22 (:REWRITE DEFAULT-<-2))
     (20 20 (:REWRITE DEFAULT-CAR))
     (20 8 (:REWRITE DEFAULT-*-2))
     (18 14 (:REWRITE DEFAULT-+-2))
     (17 17
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (16 14 (:REWRITE DEFAULT-+-1))
     (16 4 (:REWRITE O-P-O-INFP-CAR))
     (12 8 (:REWRITE DEFAULT-*-1))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (10 2
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (8 8 (:TYPE-PRESCRIPTION O-P))
     (8 4 (:REWRITE ZIP-OPEN))
     (8 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 2 (:DEFINITION APPLY$-BADGEP))
     (4 4
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 4 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (2 2 (:TYPE-PRESCRIPTION MOD))
     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2 (:DEFINITION MOD)))
(RP::AND-LIST-HASH)
(RP::INTEGERP-OF-AND-LIST-HASH)
(RP::CREATE-AND-LIST-INSTANCE)
(RP::RP-TERMP-OF-CREATE-AND-LIST-INSTANCE
     (15 15 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE DEFAULT-CDR))
     (5 1
        (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (4 1
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3 1 (:DEFINITION QUOTEP))
     (1 1 (:TYPE-PRESCRIPTION QUOTEP))
     (1 1
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::VALID-PP-P)
(RP::PP-TO-PP-LST)
(RP::VALID-PP-LST-P)
(RP::VALID-PP-LST-LST-P)
(RP::PP-LST-TO-PP$INLINE)
(RP::PP-LIST-ORDER-AUX (58 28 (:REWRITE DEFAULT-+-2))
                       (45 3 (:DEFINITION LENGTH))
                       (39 28 (:REWRITE DEFAULT-+-1))
                       (33 3 (:DEFINITION LEN))
                       (30 1 (:REWRITE O<=-O-FINP-DEF))
                       (24 6 (:REWRITE COMMUTATIVITY-OF-+))
                       (24 6 (:DEFINITION INTEGER-ABS))
                       (18 9 (:REWRITE DEFAULT-CDR))
                       (9 9
                          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                       (9 7 (:REWRITE DEFAULT-<-2))
                       (9 6 (:REWRITE STR::CONSP-OF-EXPLODE))
                       (8 8 (:REWRITE FOLD-CONSTS-IN-+))
                       (8 7 (:REWRITE DEFAULT-<-1))
                       (7 7 (:REWRITE DEFAULT-CAR))
                       (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                       (6 3
                          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                       (4 4
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                       (4 1 (:REWRITE O-P-O-INFP-CAR))
                       (4 1 (:REWRITE AC-<))
                       (3 3 (:TYPE-PRESCRIPTION LEN))
                       (3 3
                          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                       (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                       (3 3 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                       (3 3 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                       (3 3
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (3 3
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                       (3 3 (:REWRITE DEFAULT-REALPART))
                       (3 3 (:REWRITE DEFAULT-NUMERATOR))
                       (3 3 (:REWRITE DEFAULT-IMAGPART))
                       (3 3 (:REWRITE DEFAULT-DENOMINATOR))
                       (3 3
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                       (2 2
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                       (2 2
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                       (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                       (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                       (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::BOOLEANP-OF-PP-LIST-ORDER-AUX.EQUALS
     (28 28 (:REWRITE DEFAULT-CAR))
     (14 1 (:DEFINITION RP::LEXORDER2))
     (6 6 (:REWRITE DEFAULT-CDR))
     (3 1 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (2 2
        (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER)))
(RP::PP-LIST-ORDER)
(RP::BOOLEANP-OF-PP-LIST-ORDER.EQUALS
     (10 2 (:DEFINITION LEN))
     (10 1 (:REWRITE LEN-WHEN-PREFIXP))
     (6 2 (:REWRITE DEFAULT-<-2))
     (6 2 (:REWRITE DEFAULT-<-1))
     (4 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:TYPE-PRESCRIPTION PREFIXP))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
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
(RP::PP-TERM-P (2906 120 (:DEFINITION RP::EX-FROM-RP))
               (1778 120 (:REWRITE RP::NOT-INCLUDE-RP))
               (1688 138 (:DEFINITION RP::INCLUDE-FNC))
               (942 942 (:REWRITE RP::MEASURE-LEMMA1))
               (516 3 (:DEFINITION RP::PP-TERM-P))
               (437 147 (:DEFINITION QUOTEP))
               (327 12 (:REWRITE O<=-O-FINP-DEF))
               (292 292 (:REWRITE RP::MEASURE-LEMMA1-2))
               (258 258
                    (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
               (236 43 (:REWRITE O-P-O-INFP-CAR))
               (226 58 (:REWRITE RP::CONS-COUNT-ATOM))
               (153 9 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
               (120 120
                    (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
               (107 43 (:REWRITE O-P-DEF-O-FINP-1))
               (100 24 (:REWRITE RP::MEASURE-LEMMA7-2))
               (90 9
                   (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
               (80 16 (:REWRITE RP::MEASURE-LEMMA6-5))
               (64 64 (:TYPE-PRESCRIPTION O-FINP))
               (48 8 (:REWRITE O-FIRST-EXPT-<))
               (36 18 (:REWRITE DEFAULT-<-2))
               (36 18 (:REWRITE DEFAULT-<-1))
               (36 12 (:REWRITE AC-<))
               (34 34
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
               (32 16 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
               (24 12 (:REWRITE O-INFP-O-FINP-O<=))
               (18 18
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
               (18 18
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
               (16 8 (:REWRITE O-FIRST-COEFF-<))
               (12 12
                   (:REWRITE |a < b & b < c  =>  a < c|))
               (9 9 (:TYPE-PRESCRIPTION QUOTEP))
               (9 9 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::PP-TERM-LIST-P)
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
(RP::MERGE-SORTED-AND$-LISTS (377 29 (:REWRITE RP::POS-LEN-IMPLIES))
                             (353 163 (:REWRITE DEFAULT-+-2))
                             (240 163 (:REWRITE DEFAULT-+-1))
                             (166 5 (:REWRITE O<=-O-FINP-DEF))
                             (120 30 (:DEFINITION INTEGER-ABS))
                             (106 64 (:REWRITE DEFAULT-<-2))
                             (106 2 (:DEFINITION RP::LEXORDER2))
                             (74 64 (:REWRITE DEFAULT-<-1))
                             (60 15 (:DEFINITION LENGTH))
                             (58 58 (:REWRITE DEFAULT-CAR))
                             (58 58 (:LINEAR LEN-WHEN-PREFIXP))
                             (48 48 (:REWRITE DEFAULT-CDR))
                             (44 44 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                             (30 30 (:REWRITE DEFAULT-UNARY-MINUS))
                             (30 15
                                 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                             (29 29 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                             (29 29 (:LINEAR BOUNDS-POSITION-EQUAL))
                             (28 5 (:REWRITE AC-<))
                             (15 15
                                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                             (15 15 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                             (15 15
                                 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                             (15 15
                                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                             (15 15
                                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                             (15 15 (:REWRITE DEFAULT-REALPART))
                             (15 15 (:REWRITE DEFAULT-NUMERATOR))
                             (15 15 (:REWRITE DEFAULT-IMAGPART))
                             (15 15 (:REWRITE DEFAULT-DENOMINATOR))
                             (15 5 (:REWRITE O-INFP-O-FINP-O<=))
                             (12 12
                                 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                             (12 3 (:REWRITE O-P-O-INFP-CAR))
                             (9 9
                                (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                             (6 6
                                (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                             (6 6
                                (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                             (6 2 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
                             (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
                             (4 4
                                (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER)))
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
     (47135 4106 (:REWRITE RP::POS-LEN-IMPLIES))
     (42294 114
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (35522 1350 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (33310 31828 (:REWRITE DEFAULT-CDR))
     (30200 2160
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (16030 14276 (:REWRITE DEFAULT-CAR))
     (8100 8100 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (7216 4013 (:REWRITE DEFAULT-<-2))
     (7150 143
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (7020 7020 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (6700 6700 (:LINEAR LEN-WHEN-PREFIXP))
     (6480 6480
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (4800 1371 (:REWRITE O-P-O-INFP-CAR))
     (4320 4320
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (4013 4013
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (4013 4013 (:REWRITE DEFAULT-<-1))
     (3780 3780 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (3350 3350 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (3350 3350 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (530 10 (:DEFINITION RP::LEXORDER2))
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
     (117 117
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (30 10
         (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (20 20
         (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER)))
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
     (24375 22958 (:REWRITE DEFAULT-CDR))
     (22128 1568
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (12485 10318 (:REWRITE DEFAULT-CAR))
     (7188 106
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (5880 5880 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (5272 2930 (:REWRITE DEFAULT-<-2))
     (5096 5096 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (4940 4940 (:LINEAR LEN-WHEN-PREFIXP))
     (4704 4704
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (3490 969 (:REWRITE O-P-O-INFP-CAR))
     (3136 3136
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (3129 3129
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2930 2930 (:REWRITE DEFAULT-<-1))
     (2744 2744 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2470 2470 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (2470 2470 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (530 10 (:DEFINITION RP::LEXORDER2))
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
     (100 100
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (88 88 (:TYPE-PRESCRIPTION O-FINP))
     (68 68 (:TYPE-PRESCRIPTION FLOOR))
     (68 34 (:REWRITE DEFAULT-UNARY-MINUS))
     (68 34 (:REWRITE DEFAULT-+-2))
     (34 34 (:REWRITE DEFAULT-+-1))
     (30 10
         (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (20 20
         (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER)))
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
     (13824 840
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (13775 107
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (13229 632 (:REWRITE ACL2-NUMBERP-X))
     (11152 289 (:REWRITE RATIONALP-X))
     (9755 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (8794 225
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (8159 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (7595 160 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (6287 4 (:DEFINITION RP::SORT-AND$-LIST))
     (6248 351
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3835 3460 (:REWRITE DEFAULT-CDR))
     (3026 40
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2223 1322 (:REWRITE DEFAULT-CAR))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1620 1620
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1552 54 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1454 840
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1073 163
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (1053 1053
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (985 985 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (984 840 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (846 842
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (842 842
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (840 840
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (840 840 (:REWRITE |(equal c (/ x))|))
     (840 840 (:REWRITE |(equal c (- x))|))
     (840 840 (:REWRITE |(equal (/ x) c)|))
     (840 840 (:REWRITE |(equal (/ x) (/ y))|))
     (840 840 (:REWRITE |(equal (- x) c)|))
     (840 840 (:REWRITE |(equal (- x) (- y))|))
     (776 4 (:DEFINITION RP::LEXORDER2-))
     (772 4 (:DEFINITION RP::LEXORDER2))
     (747 747 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (702 702
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (692 692 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (644 36 (:DEFINITION ALL-NILS))
     (632 632
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (555 351 (:REWRITE DEFAULT-LESS-THAN-2))
     (542 147
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (534 335
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (531 159 (:REWRITE DEFAULT-PLUS-2))
     (520 520 (:LINEAR LEN-WHEN-PREFIXP))
     (458 458 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (403 381 (:REWRITE REDUCE-INTEGERP-+))
     (381 381 (:REWRITE INTEGERP-MINUS-X))
     (381 381
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (381 381 (:META META-INTEGERP-CORRECT))
     (379 335
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (374 4 (:REWRITE |(+ x (if a b c))|))
     (370 370
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (353 351 (:REWRITE DEFAULT-LESS-THAN-1))
     (351 351 (:REWRITE THE-FLOOR-BELOW))
     (351 351 (:REWRITE THE-FLOOR-ABOVE))
     (345 345
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (345 345
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (341 337
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (337 337 (:REWRITE INTEGERP-<-CONSTANT))
     (337 337 (:REWRITE CONSTANT-<-INTEGERP))
     (337 337
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (337 337
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (337 337
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (337 337
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (337 337 (:REWRITE |(< c (- x))|))
     (337 337
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (337 337
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (337 337
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (337 337
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (337 337 (:REWRITE |(< (/ x) (/ y))|))
     (337 337 (:REWRITE |(< (- x) c)|))
     (337 337 (:REWRITE |(< (- x) (- y))|))
     (336 7
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (335 335 (:REWRITE SIMPLIFY-SUMS-<))
     (308 262
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (302 84 (:REWRITE O-P-O-INFP-CAR))
     (295 295 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (289 289 (:REWRITE REDUCE-RATIONALP-+))
     (289 289 (:REWRITE REDUCE-RATIONALP-*))
     (289 289 (:REWRITE RATIONALP-MINUS-X))
     (289 289
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (289 289 (:META META-RATIONALP-CORRECT))
     (276 276 (:REWRITE |(< 0 (* x y))|))
     (262 262 (:REWRITE |(< 0 (/ x))|))
     (261 261
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (260 260 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (260 260 (:LINEAR BOUNDS-POSITION-EQUAL))
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
     (42 42 (:REWRITE |(equal x (if a b c))|))
     (42 42 (:REWRITE |(equal (if a b c) x)|))
     (36 16 (:REWRITE RP::RP-TERMP-CADDR))
     (36 16 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
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
     (20 4 (:REWRITE RP::SORT-MEASURE-LEMMA1-V2))
     (18 18 (:REWRITE |(* (- x) y)|))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (16 4 (:REWRITE RP::RP-TERMP-CADDDR))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 4 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (10 2 (:REWRITE |(+ y x)|))
     (8 8
        (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
     (8 8 (:TYPE-PRESCRIPTION O-FINP))
     (7 7
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE DEFAULT-FLOOR-1))
     (5 5 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:TYPE-PRESCRIPTION ABS))
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
(RP::MERGE-SORTED-PP-LISTS (598 46 (:REWRITE RP::POS-LEN-IMPLIES))
                           (458 207 (:REWRITE DEFAULT-+-2))
                           (310 207 (:REWRITE DEFAULT-+-1))
                           (298 60 (:REWRITE DEFAULT-CDR))
                           (205 5 (:REWRITE O<=-O-FINP-DEF))
                           (168 66 (:REWRITE DEFAULT-CAR))
                           (160 40 (:DEFINITION INTEGER-ABS))
                           (153 91 (:REWRITE DEFAULT-<-2))
                           (104 26 (:REWRITE O-P-O-INFP-CAR))
                           (101 91 (:REWRITE DEFAULT-<-1))
                           (92 92 (:LINEAR LEN-WHEN-PREFIXP))
                           (80 20 (:DEFINITION LENGTH))
                           (66 66 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                           (46 46 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                           (46 46 (:LINEAR BOUNDS-POSITION-EQUAL))
                           (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
                           (40 20
                               (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                           (31 5 (:REWRITE AC-<))
                           (20 20
                               (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                           (20 20 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                           (20 20
                               (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                           (20 20
                               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                           (20 20
                               (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                           (20 20 (:REWRITE DEFAULT-REALPART))
                           (20 20 (:REWRITE DEFAULT-NUMERATOR))
                           (20 20 (:REWRITE DEFAULT-IMAGPART))
                           (20 20 (:REWRITE DEFAULT-DENOMINATOR))
                           (20 20
                               (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                           (15 15
                               (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                           (15 5 (:REWRITE O-INFP-O-FINP-O<=))
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
(RP::SORT-PP-LISTS (26190 4 (:DEFINITION RP::EX-FROM-RP))
                   (25264 8 (:DEFINITION APPLY$-BADGEP))
                   (23660 1836 (:REWRITE RP::MEASURE-LEMMA1))
                   (18550 1594 (:REWRITE RP::SORT-MEASURE-LEMMA2))
                   (15198 16
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (14744 46
                          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (14738 4 (:REWRITE RP::NOT-INCLUDE-RP))
                   (14726 4 (:DEFINITION RP::INCLUDE-FNC))
                   (14670 8 (:DEFINITION TRUE-LISTP))
                   (12876 40
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (12812 24 (:DEFINITION RP::RP-TERMP))
                   (11894 1352 (:REWRITE RP::MEASURE-LEMMA1-2))
                   (10791 2325 (:REWRITE DEFAULT-CDR))
                   (10784 8 (:DEFINITION RP::FALIST-CONSISTENT))
                   (10778 110
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (9211 465
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                   (8256 8
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (8098 1004 (:REWRITE DEFAULT-CAR))
                   (6862 122 (:REWRITE LEN-WHEN-PREFIXP))
                   (4632 32 (:DEFINITION SUBSETP-EQUAL))
                   (3712 120
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                   (3674 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (2864 240 (:DEFINITION MEMBER-EQUAL))
                   (2786 80 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                   (2188 120
                         (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                   (2186 16 (:DEFINITION RP::RP-TERM-LISTP))
                   (1800 128
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (1748 1748 (:LINEAR LEN-WHEN-PREFIXP))
                   (1185 465
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                   (874 874 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                   (874 874 (:LINEAR BOUNDS-POSITION-EQUAL))
                   (774 774 (:TYPE-PRESCRIPTION RP::RP-TERMP))
                   (761 761
                        (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (751 465 (:REWRITE DEFAULT-<-2))
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
                   (104 26 (:REWRITE RP::RP-TERMP-CADDDDR))
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
(RP::PP-TERM-TO-PP-LISTS (130 42 (:REWRITE RP::CONS-COUNT-ATOM))
                         (104 4 (:REWRITE O<=-O-FINP-DEF))
                         (44 44 (:REWRITE RP::MEASURE-LEMMA1))
                         (44 11 (:REWRITE O-P-O-INFP-CAR))
                         (40 8 (:REWRITE RP::MEASURE-LEMMA7-2))
                         (18 18
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                         (17 17 (:REWRITE DEFAULT-CDR))
                         (12 4 (:REWRITE AC-<))
                         (11 11 (:REWRITE O-P-DEF-O-FINP-1))
                         (11 11 (:REWRITE DEFAULT-CAR))
                         (10 10
                             (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                         (8 4 (:REWRITE O-INFP-O-FINP-O<=))
                         (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
                         (4 2 (:REWRITE DEFAULT-<-2))
                         (4 2 (:REWRITE DEFAULT-<-1))
                         (2 2
                            (:REWRITE RP::EQUALITY-MEASURE-LEMMA1)))
(RP::PP-LISTS-P-OF-PP-TERM-TO-PP-LISTS
     (105889 300
             (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (98065 100 (:DEFINITION TRUE-LISTP))
     (70429 200 (:DEFINITION RP::RP-TERM-LISTP))
     (68347 700
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (65241 700 (:DEFINITION QUOTEP))
     (63017 400
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (62699 423 (:DEFINITION APPLY$-BADGEP))
     (52274 400 (:DEFINITION SUBSETP-EQUAL))
     (44274 3000 (:DEFINITION MEMBER-EQUAL))
     (32542 700
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (32448 300 (:DEFINITION RP::RP-TERMP))
     (30036 29640 (:REWRITE DEFAULT-CDR))
     (27988 1000 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (27746 1600
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (20730 100 (:DEFINITION RP::FALIST-CONSISTENT))
     (17515 17515 (:REWRITE DEFAULT-CAR))
     (16130 100
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (7400 7400 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (6000 6000 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (5200 5200 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (4996 1366 (:REWRITE O-P-O-INFP-CAR))
     (4800 4800
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (3200 3200
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (3200 900 (:REWRITE RP::IS-IF-RP-TERMP))
     (2800 2800 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2483 200 (:DEFINITION NATP))
     (2200 2200
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1700 1700
           (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (1454 1454 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (1300 400 (:REWRITE RP::RP-TERMP-CADR))
     (1298 1166 (:REWRITE O-P-DEF-O-FINP-1))
     (1052 423 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1000 1000
           (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (1000 200 (:REWRITE RP::RP-TERMP-CADDDR))
     (900 900
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (900 300 (:REWRITE RP::RP-TERMP-CADDR))
     (900 300 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (800 800 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (747 300
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (712 200
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (700 700 (:TYPE-PRESCRIPTION QUOTEP))
     (618 300
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (600 600 (:TYPE-PRESCRIPTION LEN))
     (600 100 (:DEFINITION ALL-NILS))
     (500 500 (:TYPE-PRESCRIPTION ALL-NILS))
     (500 100
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (412 200
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (300 300
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (300 300
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (258 258
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (204 204
          (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (200 200 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (200 200
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (200 200 (:LINEAR LEN-WHEN-PREFIXP))
     (132 132 (:TYPE-PRESCRIPTION O-FINP))
     (100 100
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (100 100 (:REWRITE DEFAULT-<-2))
     (100 100 (:REWRITE DEFAULT-<-1))
     (100 100 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (100 100 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::PP-TERM-TO-PP-LISTS
     (44636 51
            (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (43304 17 (:DEFINITION TRUE-LISTP))
     (38600 34 (:DEFINITION RP::RP-TERM-LISTP))
     (38247 119
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (38207 236 (:DEFINITION QUOTEP))
     (37338 68
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (37287 68 (:DEFINITION APPLY$-BADGEP))
     (35520 68 (:DEFINITION SUBSETP-EQUAL))
     (34160 510 (:DEFINITION MEMBER-EQUAL))
     (25956 618
            (:DEFINITION RP::PP-TERM-TO-PP-LISTS))
     (21372 272
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (16634 16634 (:REWRITE DEFAULT-CDR))
     (16407 170 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (10608 10608 (:REWRITE DEFAULT-CAR))
     (5539 119
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (5524 51 (:DEFINITION RP::RP-TERMP))
     (3529 17 (:DEFINITION RP::FALIST-CONSISTENT))
     (3110 3110
           (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2747 17
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1214 293 (:REWRITE O-P-O-INFP-CAR))
     (1134 78 (:DEFINITION RP::INCLUDE-FNC))
     (1020 1020 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (884 884 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (816 816
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (645 39
          (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (544 544
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (544 153 (:REWRITE RP::IS-IF-RP-TERMP))
     (518 518 (:TYPE-PRESCRIPTION O-P))
     (476 476 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (414 34 (:DEFINITION NATP))
     (403 259 (:REWRITE O-P-DEF-O-FINP-1))
     (374 374
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (372 39
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (289 289
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (255 255 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (221 68 (:REWRITE RP::RP-TERMP-CADR))
     (175 175 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (172 68 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (170 170
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (170 34 (:REWRITE RP::RP-TERMP-CADDDR))
     (158 158 (:TYPE-PRESCRIPTION QUOTEP))
     (156 156
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (153 153
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (153 51 (:REWRITE RP::RP-TERMP-CADDR))
     (153 51 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (144 144 (:TYPE-PRESCRIPTION O-FINP))
     (123 51
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (119 34
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (102 51
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (102 17 (:DEFINITION ALL-NILS))
     (85 85 (:TYPE-PRESCRIPTION ALL-NILS))
     (85 17
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (78 78
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
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
     (1240 1236 (:REWRITE DEFAULT-CDR))
     (1096 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1080 64
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (872 8 (:DEFINITION RP::FALIST-CONSISTENT))
     (731 723 (:REWRITE DEFAULT-CAR))
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
(RP::PP-REMOVE-EXTRANEOUS-SC
     (327 12 (:REWRITE O<=-O-FINP-DEF))
     (210 58 (:REWRITE RP::CONS-COUNT-ATOM))
     (100 24 (:REWRITE RP::MEASURE-LEMMA7-2))
     (99 45 (:REWRITE DEFAULT-CAR))
     (92 19 (:REWRITE O-P-O-INFP-CAR))
     (82 54 (:REWRITE DEFAULT-CDR))
     (80 16 (:REWRITE RP::MEASURE-LEMMA6-5))
     (66 66 (:REWRITE RP::MEASURE-LEMMA1-2))
     (48 8 (:REWRITE O-FIRST-EXPT-<))
     (36 18 (:REWRITE DEFAULT-<-2))
     (36 18 (:REWRITE DEFAULT-<-1))
     (36 12 (:REWRITE AC-<))
     (35 19 (:REWRITE O-P-DEF-O-FINP-1))
     (34 34
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
     (32 16 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (26 26 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (24 12 (:REWRITE O-INFP-O-FINP-O<=))
     (18 18
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (18 18
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (16 16 (:TYPE-PRESCRIPTION O-FINP))
     (16 8 (:REWRITE O-FIRST-COEFF-<))
     (12 12
         (:REWRITE |a < b & b < c  =>  a < c|))
     (1 1
        (:TYPE-PRESCRIPTION RP::PP-REMOVE-EXTRANEOUS-SC)))
(RP::PP-TERM-P-OF-PP-REMOVE-EXTRANEOUS-SC
     (41567 9255 (:REWRITE O-P-O-INFP-CAR))
     (15345 929
            (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (13954 9179 (:REWRITE O-P-DEF-O-FINP-1))
     (12731 32
            (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (12582 45 (:DEFINITION RP::RP-TERMP))
     (11953 2387
            (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (8343 931
           (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (7936 40 (:DEFINITION RP::FALIST-CONSISTENT))
     (6650 6650
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (6398 6398 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (6118 38
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3980 3980 (:TYPE-PRESCRIPTION O-FINP))
     (2387 2387
           (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (1401 155 (:REWRITE RP::IS-IF-RP-TERMP))
     (1145 77 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (952 164
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (655 5
          (:REWRITE RP::RP-TERMP-EXTRACT-FROM-RP))
     (655 5 (:REWRITE RP::RP-TERMP-EX-FROM-RP))
     (655 5
          (:REWRITE RP::EXTRACT-FROM-RP-PSEUDO-TERM-LISTP))
     (600 164 (:DEFINITION APPLY$-BADGEP))
     (400 164 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (342 342
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (268 78 (:REWRITE RP::RP-TERMP-CADR))
     (245 45
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (233 233
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (182 77 (:REWRITE RP::RP-TERMP-CADDR))
     (164 164 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (90 90
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (90 45
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (22 4 (:REWRITE O-INFP->NEQ-0))
     (20 5
         (:REWRITE RP::PSEUDO-TERMLISTP-EXTRACT-FROM-RP))
     (8 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::PP-FLATTEN)
(RP::VALID-SINGLE-BITP$INLINE)
(RP::VALID-SINGLE-BITP-IMPLIES)
(RP::SORT-SUM-META-AUX-AUX)
(RP::LEMMA1 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
            (6 6 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
            (6 6 (:LINEAR BOUNDS-POSITION-EQUAL))
            (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
            (4 2 (:REWRITE DEFAULT-+-2))
            (2 2 (:REWRITE DEFAULT-CDR))
            (2 2 (:REWRITE DEFAULT-+-1)))
(RP::SORT-SUM-META-AUX-AUX (45 45 (:REWRITE DEFAULT-CAR))
                           (14 14
                               (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                           (14 7 (:DEFINITION TRUE-LISTP))
                           (4 1 (:REWRITE O-P-O-INFP-CAR))
                           (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::PP-LIST-ENTRY-P-OF-SORT-SUM-META-AUX-AUX
     (63 63
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (12 4 (:REWRITE O-P-O-INFP-CAR))
     (8 4 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:TYPE-PRESCRIPTION O-FINP))
     (4 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2 1 (:DEFINITION APPLY$-BADGEP))
     (1 1 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (1 1 (:DEFINITION WEAK-APPLY$-BADGE-P)))
(RP::SORT-SUM-META-AUX (37 36 (:REWRITE RP::MEASURE-LEMMA1))
                       (35 12 (:REWRITE RP::MEASURE-LEMMA1-2))
                       (22 1 (:REWRITE O<=-O-FINP-DEF))
                       (18 12 (:REWRITE DEFAULT-CDR))
                       (14 6 (:REWRITE RP::CONS-COUNT-ATOM))
                       (4 4
                          (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                       (4 1 (:REWRITE O-P-O-INFP-CAR))
                       (3 1 (:REWRITE AC-<))
                       (2 2 (:REWRITE RP::MEASURE-LEMMA7-2))
                       (2 2 (:REWRITE RP::EX-FROM-RP-X2))
                       (2 2
                          (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                       (2 2 (:REWRITE DEFAULT-CAR))
                       (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                       (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                       (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::PP-LISTS-P-OF-SORT-SUM-META-AUX
     (8445 21
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (7899 7 (:DEFINITION TRUE-LISTP))
     (5967 14 (:DEFINITION RP::RP-TERM-LISTP))
     (5820 49
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (5603 49 (:DEFINITION QUOTEP))
     (5449 28
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (5428 29 (:DEFINITION APPLY$-BADGEP))
     (4706 28 (:DEFINITION SUBSETP-EQUAL))
     (4146 210 (:DEFINITION MEMBER-EQUAL))
     (3039 3039 (:REWRITE DEFAULT-CDR))
     (2600 112
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2415 70 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (2275 49
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2268 21 (:DEFINITION RP::RP-TERMP))
     (1533 1533 (:REWRITE DEFAULT-CAR))
     (1449 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (1127 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (420 420 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (364 364 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (336 336
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (322 91 (:REWRITE O-P-O-INFP-CAR))
     (224 224
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (224 63 (:REWRITE RP::IS-IF-RP-TERMP))
     (196 196 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (169 14 (:DEFINITION NATP))
     (154 154
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (119 119
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (103 103 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (91 28 (:REWRITE RP::RP-TERMP-CADR))
     (77 77 (:REWRITE O-P-DEF-O-FINP-1))
     (72 29 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (70 70
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (70 14 (:REWRITE RP::RP-TERMP-CADDDR))
     (63 63
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (63 21 (:REWRITE RP::RP-TERMP-CADDR))
     (63 21 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (56 56 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (50 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (49 49 (:TYPE-PRESCRIPTION QUOTEP))
     (49 14
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (42 42 (:TYPE-PRESCRIPTION LEN))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (42 7 (:DEFINITION ALL-NILS))
     (35 35 (:TYPE-PRESCRIPTION ALL-NILS))
     (35 7
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (28 14
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (21 21
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (21 21
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (14 14 (:LINEAR LEN-WHEN-PREFIXP))
     (7 7
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL)))
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
     (1982 1978 (:REWRITE DEFAULT-CDR))
     (1939 82
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1839 9 (:DEFINITION RP::FALIST-CONSISTENT))
     (1673 70 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1540 112
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1428 9
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1120 1116 (:REWRITE DEFAULT-CAR))
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
     (56 4 (:DEFINITION RP::LEXORDER2))
     (54 18 (:REWRITE RP::RP-TERMP-CADDR))
     (54 18 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (42 42 (:TYPE-PRESCRIPTION LEN))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (42 21
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (42 7 (:DEFINITION ALL-NILS))
     (38 12 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (35 35 (:TYPE-PRESCRIPTION ALL-NILS))
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
     (12 4 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (12 3 (:DEFINITION RP::INCLUDE-FNC))
     (8 8
        (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
     (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (7 7 (:LINEAR BOUNDS-POSITION-EQUAL))
     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC)))
(RP::RP-TERM-LISTP-SORT-AND$-LIST
     (4281 16 (:DEFINITION RP::RP-TERMP))
     (2853 16 (:DEFINITION RP::FALIST-CONSISTENT))
     (2192 15
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1823 1823 (:REWRITE DEFAULT-CDR))
     (1370 51
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (1259 1259 (:REWRITE DEFAULT-CAR))
     (1234 55 (:DEFINITION QUOTEP))
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
     (120 120 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (120 30 (:REWRITE RP::RP-TERMP-CADDR))
     (113 10 (:DEFINITION RP::LEXORDER2))
     (104 104 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (99 99 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (64 64
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
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
     (30 10
         (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (28 28
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (27 27 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (21 21 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (20 20
         (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
     (20 20
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
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
     (2 2 (:TYPE-PRESCRIPTION O-FINP)))
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
     (9562 29 (:DEFINITION RP::RP-TERMP))
     (5256 4888 (:REWRITE DEFAULT-CDR))
     (5147 29 (:DEFINITION RP::FALIST-CONSISTENT))
     (4522 29
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (3401 3401 (:REWRITE DEFAULT-CAR))
     (3202 162 (:REWRITE RP::IS-IF-RP-TERMP))
     (1834 502 (:REWRITE O-P-O-INFP-CAR))
     (1007 95
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (982 68 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (550 30
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (540 30 (:DEFINITION APPLY$-BADGEP))
     (444 444 (:REWRITE O-P-DEF-O-FINP-1))
     (382 95
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (370 370
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (354 354
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (328 328
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (269 58
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (240 20 (:DEFINITION NATP))
     (207 207 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (152 38
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (126 21 (:REWRITE RP::NOT-INCLUDE-RP))
     (120 120 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (93 93
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (84 21 (:DEFINITION RP::INCLUDE-FNC))
     (80 30 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (76 76
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (70 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (70 20
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (60 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (58 58
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (36 36
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (30 30
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (21 21 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERMP-OF-PP-LISTS-TO-TERM-PP-LST
     (2708 60
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (2560 46 (:DEFINITION QUOTEP))
     (2464 22
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (2428 18 (:DEFINITION APPLY$-BADGEP))
     (1848 16 (:DEFINITION SUBSETP-EQUAL))
     (1568 1210 (:REWRITE DEFAULT-CDR))
     (1528 120 (:DEFINITION MEMBER-EQUAL))
     (1012 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1000 906 (:REWRITE DEFAULT-CAR))
     (960 64
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (936 8 (:DEFINITION RP::FALIST-CONSISTENT))
     (682 198 (:REWRITE O-P-O-INFP-CAR))
     (616 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (438 60
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (320 320 (:TYPE-PRESCRIPTION O-P))
     (308 48 (:REWRITE RP::IS-IF-RP-TERMP))
     (264 40 (:REWRITE RP::RP-TERMP-CADR))
     (240 240 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (228 228
          (:TYPE-PRESCRIPTION RP::CREATE-AND-LIST-INSTANCE))
     (208 208 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (192 192
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (164 160 (:REWRITE O-P-DEF-O-FINP-1))
     (160 160
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (128 128
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (126 18 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (124 22
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (80 8
         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (80 8 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (76 8 (:DEFINITION NATP))
     (72 4 (:DEFINITION TRUE-LISTP))
     (60 60 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (54 54 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (50 50 (:TYPE-PRESCRIPTION QUOTEP))
     (48 8 (:REWRITE RP::RP-TERMP-CADDR))
     (40 40
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (40 4 (:REWRITE RP::NOT-INCLUDE-RP))
     (32 4 (:DEFINITION RP::INCLUDE-FNC))
     (24 24 (:TYPE-PRESCRIPTION LEN))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (24 4 (:DEFINITION ALL-NILS))
     (22 22
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
     (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
     (8 4
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (8 4
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (4 4 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (4 4
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::RP-TERMP-OF-PP-REMOVE-EXTRANEOUS-SC
     (13519 13519 (:REWRITE DEFAULT-CDR))
     (9819 9819 (:REWRITE DEFAULT-CAR))
     (7192 706 (:REWRITE RP::IS-IF-RP-TERMP))
     (5572 1565 (:REWRITE O-P-O-INFP-CAR))
     (1397 1305 (:REWRITE O-P-DEF-O-FINP-1))
     (1353 230
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1053 1053
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (927 927
          (:TYPE-PRESCRIPTION RP::PP-REMOVE-EXTRANEOUS-SC))
     (705 705 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (580 36
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (558 36 (:DEFINITION APPLY$-BADGEP))
     (511 86 (:REWRITE RP::NOT-INCLUDE-RP))
     (500 126
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (340 85 (:DEFINITION RP::INCLUDE-FNC))
     (288 288
          (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (240 20 (:DEFINITION NATP))
     (230 230
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (196 49
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (126 126 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (100 100
          (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (92 92 (:TYPE-PRESCRIPTION O-FINP))
     (92 36 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (85 85 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (70 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (70 20
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (60 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (48 16
         (:REWRITE RP::RP-TERMP-CONS-CAR-TERM-SUBTERMS))
     (30 30
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1)))
(RP::RP-TERM-LISTP-OF-PP-FLATTEN
     (4179 21 (:DEFINITION RP::FALIST-CONSISTENT))
     (3234 21
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (2726 2503 (:REWRITE DEFAULT-CDR))
     (1845 1782 (:REWRITE DEFAULT-CAR))
     (1076 288 (:REWRITE O-P-O-INFP-CAR))
     (677 677
          (:TYPE-PRESCRIPTION RP::PP-REMOVE-EXTRANEOUS-SC))
     (364 90 (:REWRITE RP::IS-IF-RP-TERMP))
     (296 246 (:REWRITE O-P-DEF-O-FINP-1))
     (189 42
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (184 44 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (151 151
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (137 137
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (128 16 (:DEFINITION STRIP-CDRS))
     (126 21 (:REWRITE RP::NOT-INCLUDE-RP))
     (118 118 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (96 6 (:DEFINITION RP::RP-EQUAL))
     (88 22
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (84 21 (:DEFINITION RP::INCLUDE-FNC))
     (84 6 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
     (70 5 (:DEFINITION RP::LEXORDER2))
     (48 48
         (:TYPE-PRESCRIPTION RP::PP-LISTS-TO-TERM-PP-LST))
     (42 42
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (21 21 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (21 21
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (20 20 (:TYPE-PRESCRIPTION O-FINP))
     (15 5 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (10 10
         (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (6 6
        (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::RP-TERM-LISTP-OF-SORT-SUM-META-AUX-AUX
     (322 102 (:REWRITE RP::RP-TERMP-CADR))
     (300 300
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (162 27 (:REWRITE RP::NOT-INCLUDE-RP))
     (156 96 (:REWRITE RP::RP-TERMP-CADDR))
     (156 96 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (108 27 (:DEFINITION RP::INCLUDE-FNC))
     (101 95
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (95 95
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (89 53
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (62 7
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (53 53 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (48 7 (:DEFINITION APPLY$-BADGEP))
     (27 27 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (27 7
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (21 3 (:DEFINITION NATP))
     (14 7 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (13 13 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (12 12 (:REWRITE RP::RP-TERMP-CADDDR))
     (12 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4
        (:REWRITE RP::RP-TERMP-EXTRACT-FROM-RP))
     (4 4 (:REWRITE RP::RP-TERMP-EX-FROM-RP)))
(RP::RP-TERM-LIST-LISTP-STRIP-CDRS-SORT-SUM-META-AUX
     (1176 21 (:DEFINITION RP::RP-TERMP))
     (387 386 (:REWRITE DEFAULT-CDR))
     (318 317 (:REWRITE DEFAULT-CAR))
     (191 191
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (189 28
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (147 147
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (126 21 (:REWRITE RP::NOT-INCLUDE-RP))
     (84 21 (:DEFINITION RP::INCLUDE-FNC))
     (77 7 (:DEFINITION RP::RP-TERM-LISTP))
     (42 42
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (28 28 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (21 21 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (20 5
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP)))
(RP::RP-TERMP-OF-SORT-SUM-META.RESULT
     (597 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (462 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (335 327 (:REWRITE DEFAULT-CDR))
     (243 243 (:REWRITE DEFAULT-CAR))
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
     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (3 3
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::VALID-SC-SUBTERMS-LST)
(RP::VALID-SC-SUBTERMS-CUT-LIST-BY-HALF
     (2076 3 (:DEFINITION RP::VALID-SC))
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
     (405 3 (:DEFINITION RP::EVAL-AND-ALL))
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
     (6 6 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
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
     (2070 3 (:DEFINITION RP::VALID-SC))
     (1803 82 (:DEFINITION RP::INCLUDE-FNC))
     (813 3
          (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (801 3 (:DEFINITION RP::RP-TERMP))
     (737 711 (:REWRITE DEFAULT-CDR))
     (708 664 (:REWRITE DEFAULT-CAR))
     (621 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (483 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (452 110 (:REWRITE O-P-O-INFP-CAR))
     (405 3 (:DEFINITION RP::EVAL-AND-ALL))
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
     (56 4 (:DEFINITION RP::LEXORDER2))
     (54 54
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (48 6 (:DEFINITION RP::IS-FALIST))
     (45 3 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (36 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (33 3 (:REWRITE RP::NOT-INCLUDE-RP))
     (33 3 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (30 30 (:TYPE-PRESCRIPTION O-FINP))
     (27 27
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
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
     (12 4 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (12 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 6 (:REWRITE RP::VALID-SC-CADDR))
     (8 8
        (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
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
     (6 6 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
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
     (3 3
        (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL)))
(RP::VALID-SC-SUBTERMS-SORT-AND$-LIST
     (5094 7 (:DEFINITION RP::VALID-SC))
     (3409 104 (:DEFINITION RP::INCLUDE-FNC))
     (2151 7
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (2109 11 (:DEFINITION RP::RP-TERMP))
     (1493 11 (:DEFINITION RP::FALIST-CONSISTENT))
     (1127 7
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (945 7 (:DEFINITION RP::EVAL-AND-ALL))
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
     (98 7 (:DEFINITION RP::LEXORDER2))
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
     (56 56 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (55 11
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (53 53 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (48 48 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
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
     (21 7 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (18 18 (:TYPE-PRESCRIPTION QUOTEP))
     (16 8 (:REWRITE DEFAULT-<-2))
     (14 14
         (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
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
     (14 14 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
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
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 4 (:REWRITE DEFAULT-+-2))
     (7 7 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (7 7 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (4 4 (:REWRITE DEFAULT-+-1)))
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
     (9979 21 (:DEFINITION RP::VALID-SC))
     (5607 41 (:DEFINITION RP::EVAL-AND-ALL))
     (4650 296 (:DEFINITION RP::INCLUDE-FNC))
     (4595 4041 (:REWRITE DEFAULT-CDR))
     (4239 212
           (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (3167 2795 (:REWRITE DEFAULT-CAR))
     (2584 62 (:DEFINITION RP::RP-TRANS))
     (2556 18 (:REWRITE RP::VALID-SC-EX-FROM-RP-2))
     (2166 495 (:REWRITE O-P-O-INFP-CAR))
     (1349 123
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (1266 1266
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (1116 62 (:DEFINITION RP::TRANS-LIST))
     (1080 4
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (1068 4 (:DEFINITION RP::RP-TERMP))
     (1054 62
           (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (917 382 (:DEFINITION QUOTEP))
     (868 62 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (828 4 (:DEFINITION RP::FALIST-CONSISTENT))
     (744 62 (:DEFINITION RP::IS-SYNP$INLINE))
     (697 487 (:REWRITE O-P-DEF-O-FINP-1))
     (644 4
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (558 558
          (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (496 62 (:DEFINITION RP::IS-FALIST))
     (372 62
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (370 370
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (248 248 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (231 21 (:REWRITE RP::NOT-INCLUDE-RP))
     (225 22
          (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (211 211
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (210 210 (:TYPE-PRESCRIPTION O-FINP))
     (186 62 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (182 182
          (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (124 124
          (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (113 113
          (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (99 99 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (95 19
         (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (82 66
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (80 20
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (66 66
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (62 62
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (62 62 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (62 62
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (62 62
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (62 62
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (62 62 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (36 36
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (36 36
         (:TYPE-PRESCRIPTION RP::AND$-PP-LISTS))
     (32 16 (:REWRITE RP::IS-IF-RP-TERMP))
     (24 24 (:TYPE-PRESCRIPTION QUOTEP))
     (24 24
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (21 21
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (20 4
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (16 8 (:REWRITE RP::RP-TERMP-CADR))
     (16 8 (:REWRITE RP::RP-TERMP-CADDR))
     (16 8 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (8 8
        (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (8 4
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP)))
(RP::VALID-SC-PP-LISTS-TO-TERM-P+
     (1975 1443 (:REWRITE DEFAULT-CDR))
     (1662 1546 (:REWRITE DEFAULT-CAR))
     (1224 321 (:REWRITE O-P-O-INFP-CAR))
     (760 4 (:DEFINITION RP::EVAL-AND-ALL))
     (598 13 (:REWRITE RP::NOT-INCLUDE-RP))
     (594 4
          (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (566 10 (:DEFINITION RP::RP-TERMP))
     (488 8
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (420 50
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (340 50 (:DEFINITION APPLY$-BADGEP))
     (328 8 (:DEFINITION RP::RP-TRANS))
     (320 32 (:REWRITE RP::VALID-SC-CADR))
     (301 301 (:REWRITE O-P-DEF-O-FINP-1))
     (221 18 (:REWRITE RP::IS-IF-RP-TERMP))
     (211 12 (:REWRITE RP::RP-TERMP-CADR))
     (178 4 (:DEFINITION RP::RP-TERM-LISTP))
     (144 8 (:DEFINITION RP::TRANS-LIST))
     (128 8
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (118 50 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (112 8 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (104 32
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (96 8 (:DEFINITION NATP))
     (96 8 (:DEFINITION RP::IS-SYNP$INLINE))
     (86 86 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (72 72
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (64 8 (:DEFINITION RP::IS-FALIST))
     (50 4 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (40 40 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (40 8
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (34 34
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (32 32
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
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
     (22 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (16 16
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (16 16
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (16 8
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (16 4
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (12 12 (:TYPE-PRESCRIPTION QUOTEP))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 6 (:REWRITE RP::RP-TERMP-CADDR))
     (12 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
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
     (8 8 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
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
(RP::VALID-SC-OF-PP-REMOVE-EXTRANEOUS-SC
     (10946 90 (:DEFINITION RP::EVAL-AND-ALL))
     (7265 175 (:DEFINITION RP::RP-TRANS))
     (6728 6203 (:REWRITE DEFAULT-CDR))
     (4655 3605 (:REWRITE DEFAULT-CAR))
     (3150 175 (:DEFINITION RP::TRANS-LIST))
     (2634 131
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (2450 175 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (2100 175 (:DEFINITION RP::IS-SYNP$INLINE))
     (1792 14 (:REWRITE RP::VALID-SC-EX-FROM-RP-2))
     (1575 1575
           (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (1400 175 (:DEFINITION RP::IS-FALIST))
     (1076 232 (:REWRITE O-P-O-INFP-CAR))
     (1050 175
           (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (984 984
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (700 700 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (528 175
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (522 174 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (464 464 (:TYPE-PRESCRIPTION O-P))
     (380 232 (:REWRITE O-P-DEF-O-FINP-1))
     (350 350
          (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (337 337 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (313 74
          (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (252 84 (:REWRITE RP::NOT-INCLUDE-RP))
     (234 186
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (194 194
          (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (186 186
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (175 175
          (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (174 174 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (174 174
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (174 174
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (174 174
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (174 174 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (148 148 (:TYPE-PRESCRIPTION O-FINP))
     (43 17
         (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (8 1
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP)))
(RP::PP-FLATTEN-RETURNS-VALID-SC
     (5035 4686 (:REWRITE DEFAULT-CDR))
     (4485 216
           (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (3990 21 (:DEFINITION RP::EVAL-AND-ALL))
     (3624 3309 (:REWRITE DEFAULT-CAR))
     (2562 42
           (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (2100 252
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (1722 42 (:DEFINITION RP::RP-TRANS))
     (1701 252 (:DEFINITION APPLY$-BADGEP))
     (1290 310 (:REWRITE O-P-O-INFP-CAR))
     (1032 31 (:REWRITE RP::NOT-INCLUDE-RP))
     (1029 21
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (966 21 (:DEFINITION RP::RP-TERMP))
     (756 42 (:DEFINITION RP::TRANS-LIST))
     (672 42
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (647 647
          (:TYPE-PRESCRIPTION RP::PP-REMOVE-EXTRANEOUS-SC))
     (588 42 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (546 252 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (504 42 (:DEFINITION NATP))
     (504 42 (:DEFINITION RP::IS-SYNP$INLINE))
     (441 441 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (378 378
          (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (360 310 (:REWRITE O-P-DEF-O-FINP-1))
     (357 105
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (336 42 (:DEFINITION RP::IS-FALIST))
     (210 21 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (201 201 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (168 168 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (147 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (147 42
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (128 16 (:DEFINITION STRIP-CDRS))
     (126 63
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (126 42 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (126 21
          (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (112 112
          (:TYPE-PRESCRIPTION RP::PP-LISTS-TO-TERM-PP-LST))
     (105 105
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (105 21
          (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (96 6 (:DEFINITION RP::RP-EQUAL))
     (84 84
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (84 84
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (84 42 (:REWRITE RP::IS-IF-RP-TERMP))
     (84 21
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (84 6 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
     (70 5 (:DEFINITION RP::LEXORDER2))
     (63 63
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (63 63
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (42 42
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (42 42
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
     (42 42 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (42 42
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (42 42
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (42 42
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (42 42 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (42 21 (:REWRITE RP::RP-TERMP-CADR))
     (42 21 (:REWRITE RP::RP-TERMP-CADDR))
     (42 21 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (21 21 (:TYPE-PRESCRIPTION QUOTEP))
     (21 21
         (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (21 21 (:REWRITE RP::VALID-SC-CADDDR))
     (21 21 (:REWRITE DEFAULT-<-2))
     (21 21 (:REWRITE DEFAULT-<-1))
     (20 20 (:TYPE-PRESCRIPTION O-FINP))
     (15 5 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
     (10 10
         (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER))
     (6 6
        (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE)))
(RP::VALID-SC-OF-SORT-SUM-META-AUX-AUX
     (147 25
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (98 98
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (74 25 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (72 24 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (49 49
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (29 29
         (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (25 25
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (25 25
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (25 25 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (25 25
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (25 25
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (25 25
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (25 25 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (25 25 (:REWRITE RP::NOT-INCLUDE-RP))
     (24 24 (:REWRITE RP::VALID-SC-CADDDR))
     (24 24
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (24 24
         (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (24 24 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (24 24
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (24 24 (:DEFINITION RP::IS-SYNP$INLINE))
     (20 6 (:REWRITE O-P-O-INFP-CAR))
     (14 6 (:REWRITE O-P-DEF-O-FINP-1))
     (8 8 (:TYPE-PRESCRIPTION O-FINP))
     (7 3 (:REWRITE RP::VALID-SC-EX-FROM-RP-2))
     (1 1
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::SORT-SUM-META-AUX-RETURNS-VALID-SC
     (168 14
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (126 14
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (119 7 (:DEFINITION RP::VALID-SC-SUBTERMS))
     (105 104 (:REWRITE DEFAULT-CAR))
     (70 70
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (56 14 (:REWRITE O-P-O-INFP-CAR))
     (28 28 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (15 5 (:REWRITE RP::VALID-SC-EX-FROM-RP-2))
     (14 14 (:REWRITE O-P-DEF-O-FINP-1))
     (10 10
         (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL)))
(RP::SORT-SUM-META-RETURNS-VALID-SC
     (1662 71 (:DEFINITION RP::INCLUDE-FNC))
     (1039 1001 (:REWRITE DEFAULT-CDR))
     (950 5 (:DEFINITION RP::EVAL-AND-ALL))
     (815 5
          (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (797 737 (:REWRITE DEFAULT-CAR))
     (782 17 (:DEFINITION RP::RP-TERMP))
     (610 10
          (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (500 60
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (414 6 (:DEFINITION RP::RP-TERM-LISTP))
     (410 10 (:DEFINITION RP::RP-TRANS))
     (406 30 (:REWRITE RP::VALID-SC-CADR))
     (405 60 (:DEFINITION APPLY$-BADGEP))
     (323 37 (:REWRITE RP::IS-IF-RP-TERMP))
     (307 26 (:REWRITE RP::RP-TERMP-CADR))
     (304 76 (:REWRITE O-P-O-INFP-CAR))
     (296 22
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (220 98 (:DEFINITION QUOTEP))
     (180 10 (:DEFINITION RP::TRANS-LIST))
     (173 10 (:REWRITE RP::NOT-INCLUDE-RP))
     (160 10
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (140 10 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (130 60 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (120 10 (:DEFINITION NATP))
     (120 10 (:DEFINITION RP::IS-SYNP$INLINE))
     (105 105 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (95 5 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (90 90
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (85 25
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (80 10 (:DEFINITION RP::IS-FALIST))
     (76 76 (:REWRITE O-P-DEF-O-FINP-1))
     (63 63
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (60 12
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (45 45 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (40 40 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (40 10 (:REWRITE RP::VALID-SC-CADDR))
     (35 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (35 10
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (30 10 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (30 5 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (28 5 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (25 25
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (24 12
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (22 11 (:REWRITE RP::RP-TERMP-CADDR))
     (22 11 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (21 21 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (20 20
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (20 20
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (20 5
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (17 17 (:TYPE-PRESCRIPTION QUOTEP))
     (16 2 (:DEFINITION STRIP-CDRS))
     (15 15
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
     (10 10 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (10 10
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (10 10
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (10 10
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (10 10 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (5 5 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (5 5 (:REWRITE RP::VALID-SC-CADDDR))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1)))
