(RP::VALID-LIST-TERMP)
(RP::CONS-PP-TO-PP-LST-LST)
(RP::APPEND-PP-LST-LSTS)
(RP::S-ORDER (26260 9912 (:REWRITE RP::MEASURE-LEMMA1))
             (25402 746 (:DEFINITION RP::EX-FROM-RP))
             (16308 5292 (:REWRITE RP::MEASURE-LEMMA1-2))
             (14700 828 (:REWRITE RP::NOT-INCLUDE-RP))
             (12520 762 (:DEFINITION RP::INCLUDE-FNC))
             (11066 5290 (:REWRITE DEFAULT-CDR))
             (6846 4108 (:REWRITE DEFAULT-CAR))
             (6514 266
                   (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
             (6252 314 (:DEFINITION APPLY$-BADGEP))
             (3682 24 (:DEFINITION SUBSETP-EQUAL))
             (3296 36
                   (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
             (2410 180 (:DEFINITION MEMBER-EQUAL))
             (2252 588 (:REWRITE O-P-O-INFP-CAR))
             (2202 2202
                   (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
             (2174 60 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
             (1510 96
                   (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
             (1308 1308
                   (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
             (858 314 (:DEFINITION WEAK-APPLY$-BADGE-P))
             (676 20 (:REWRITE RP::EX-FROM-RP-X2))
             (426 100
                  (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
             (414 414 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
             (360 360 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
             (348 6 (:DEFINITION TRUE-LISTP))
             (312 312 (:REWRITE SUBSETP-IMPLIES-MEMBER))
             (288 288
                  (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
             (264 1 (:DEFINITION RP::S-ORDER))
             (242 6 (:DEFINITION LEN))
             (234 62 (:REWRITE RP::IS-IF-RP-TERMP))
             (234 6 (:DEFINITION ALL-NILS))
             (220 22
                  (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
             (192 192
                  (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
             (174 12
                  (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
             (168 168 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
             (146 12 (:DEFINITION NATP))
             (130 130 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
             (128 128
                  (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
             (113 3 (:REWRITE O<=-O-FINP-DEF))
             (112 30 (:REWRITE RP::RP-TERMP-CADR))
             (88 48 (:REWRITE RP::CONS-COUNT-ATOM))
             (60 60
                 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
             (56 24
                 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
             (48 4 (:REWRITE <<-IMPLIES-LEXORDER))
             (42 42 (:TYPE-PRESCRIPTION LEN))
             (42 18
                 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
             (32 8 (:REWRITE <<-TRICHOTOMY))
             (30 30 (:TYPE-PRESCRIPTION ALL-NILS))
             (28 28
                 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
             (28 14 (:REWRITE DEFAULT-+-2))
             (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
             (24 24 (:TYPE-PRESCRIPTION <<))
             (22 14 (:REWRITE DEFAULT-+-1))
             (18 18
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (15 3 (:REWRITE AC-<))
             (14 6
                 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
             (12 12
                 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
             (12 12 (:LINEAR LEN-WHEN-PREFIXP))
             (10 10
                 (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
             (9 3 (:REWRITE O-INFP-O-FINP-O<=))
             (8 8 (:TYPE-PRESCRIPTION O-FINP))
             (8 8 (:REWRITE <<-TRANSITIVE))
             (8 4 (:REWRITE <<-ASYMMETRIC))
             (6 6 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
             (6 6
                (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
             (6 6
                (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
             (6 6 (:REWRITE DEFAULT-<-2))
             (6 6 (:REWRITE DEFAULT-<-1))
             (6 6 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
             (6 6 (:LINEAR BOUNDS-POSITION-EQUAL))
             (4 4
                (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
             (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
             (4 4 (:REWRITE LEXORDER-TRANSITIVE))
             (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
             (3 1
                (:REWRITE RP::SMALL-ALPHORDER-SANITY)))
(RP::S-ORDER-FLAG (544 16 (:DEFINITION RP::EX-FROM-RP))
                  (418 296 (:REWRITE RP::MEASURE-LEMMA1))
                  (304 16 (:REWRITE RP::NOT-INCLUDE-RP))
                  (256 16 (:DEFINITION RP::INCLUDE-FNC))
                  (166 54 (:REWRITE DEFAULT-CDR))
                  (160 60 (:REWRITE DEFAULT-CAR))
                  (113 3 (:REWRITE O<=-O-FINP-DEF))
                  (88 48 (:REWRITE RP::CONS-COUNT-ATOM))
                  (72 72 (:REWRITE RP::MEASURE-LEMMA1-2))
                  (66 2 (:REWRITE RP::EX-FROM-RP-X2))
                  (48 48 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                  (32 32
                      (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                  (20 2
                      (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
                  (16 16
                      (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                  (16 8 (:REWRITE DEFAULT-+-2))
                  (16 8 (:REWRITE DEFAULT-+-1))
                  (15 3 (:REWRITE AC-<))
                  (9 3 (:REWRITE O-INFP-O-FINP-O<=))
                  (8 2 (:REWRITE O-P-O-INFP-CAR))
                  (4 4
                     (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                  (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
                  (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::S-ORDER-FLAG-EQUIVALENCES)
(RP::EX-FROM-RP/--LOOSE
     (3095 12
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (3092 11 (:DEFINITION APPLY$-BADGEP))
     (1386 12 (:DEFINITION SUBSETP-EQUAL))
     (1335 6
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (1146 90 (:DEFINITION MEMBER-EQUAL))
     (1128 3 (:DEFINITION TRUE-LISTP))
     (942 15
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (937 898 (:REWRITE DEFAULT-CDR))
     (918 9 (:DEFINITION RP::RP-TERMP))
     (759 30 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (720 48
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (621 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (483 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (416 416 (:REWRITE DEFAULT-CAR))
     (342 6 (:DEFINITION RP::RP-TERM-LISTP))
     (307 144 (:REWRITE DEFAULT-+-2))
     (278 8 (:REWRITE O<=-O-FINP-DEF))
     (195 144 (:REWRITE DEFAULT-+-1))
     (195 13 (:DEFINITION LENGTH))
     (180 180 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (164 16 (:DEFINITION LEN))
     (156 156 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (150 42 (:REWRITE O-P-O-INFP-CAR))
     (144 144
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (126 15
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (120 36 (:REWRITE RP::IS-IF-RP-TERMP))
     (104 26 (:REWRITE COMMUTATIVITY-OF-+))
     (104 26 (:DEFINITION INTEGER-ABS))
     (96 96
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (90 90
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (84 84 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (76 6 (:DEFINITION NATP))
     (75 15 (:DEFINITION QUOTEP))
     (74 74 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (64 64
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (63 46 (:REWRITE DEFAULT-<-2))
     (60 46 (:REWRITE DEFAULT-<-1))
     (50 18
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (48 12 (:REWRITE RP::RP-TERMP-CADDDR))
     (48 12 (:REWRITE RP::RP-TERMP-CADDDDR))
     (40 40
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (39 39
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (39 26 (:REWRITE STR::CONSP-OF-EXPLODE))
     (36 36
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (36 36
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (36 36 (:REWRITE O-P-DEF-O-FINP-1))
     (36 18
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (36 12 (:REWRITE RP::RP-TERMP-CADR))
     (36 12 (:REWRITE RP::RP-TERMP-CADDR))
     (36 12 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (36 6 (:REWRITE O-FIRST-EXPT-<))
     (34 34 (:TYPE-PRESCRIPTION LEN))
     (32 32
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (30 30
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (28 11 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (27 27
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (27 8 (:REWRITE AC-<))
     (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
     (26 13
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (24 24 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (24 12 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (24 9
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (19 19
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 3 (:DEFINITION ALL-NILS))
     (16 16 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (16 8 (:REWRITE O-INFP-O-FINP-O<=))
     (15 15 (:TYPE-PRESCRIPTION QUOTEP))
     (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
     (15 3
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (13 13
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (13 13 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (13 13
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (13 13
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (13 13 (:REWRITE DEFAULT-REALPART))
     (13 13 (:REWRITE DEFAULT-NUMERATOR))
     (13 13 (:REWRITE DEFAULT-IMAGPART))
     (13 13 (:REWRITE DEFAULT-DENOMINATOR))
     (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (12 12 (:LINEAR LEN-WHEN-PREFIXP))
     (12 6 (:REWRITE O-FIRST-COEFF-<))
     (8 8 (:REWRITE |a < b & b < c  =>  a < c|))
     (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (6 6
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (6 6 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (6 6 (:LINEAR BOUNDS-POSITION-EQUAL))
     (3 3
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::RP-TERMP-OF-EX-FROM-RP/--LOOSE
     (3230 393 (:REWRITE RP::IS-IF-RP-TERMP))
     (2920 829 (:REWRITE O-P-O-INFP-CAR))
     (697 697 (:REWRITE O-P-DEF-O-FINP-1))
     (610 117
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (585 585
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (375 375 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (290 50 (:REWRITE RP::NOT-INCLUDE-RP))
     (192 48 (:DEFINITION RP::INCLUDE-FNC))
     (146 146
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (120 20
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (80 20 (:DEFINITION APPLY$-BADGEP))
     (64 16 (:REWRITE RP::RP-TERMP-CADDDR))
     (60 20 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (48 48 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (20 20 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE)))
(RP::EX-FROM-RP/-- (108 55 (:REWRITE DEFAULT-+-2))
                   (71 55 (:REWRITE DEFAULT-+-1))
                   (67 55 (:REWRITE DEFAULT-CDR))
                   (60 4 (:DEFINITION LENGTH))
                   (44 4 (:DEFINITION LEN))
                   (43 43 (:REWRITE DEFAULT-CAR))
                   (32 8 (:DEFINITION INTEGER-ABS))
                   (26 2 (:REWRITE O<=-O-FINP-DEF))
                   (24 6 (:REWRITE O-P-O-INFP-CAR))
                   (20 4
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (18 6 (:DEFINITION APPLY$-BADGEP))
                   (12 12
                       (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                   (12 10 (:REWRITE DEFAULT-<-2))
                   (12 10 (:REWRITE DEFAULT-<-1))
                   (12 8 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (12 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (10 2
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
                   (8 4
                      (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                   (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (6 6 (:REWRITE O-P-DEF-O-FINP-1))
                   (6 2 (:REWRITE AC-<))
                   (5 1
                      (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (4 4 (:TYPE-PRESCRIPTION LEN))
                   (4 4
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (4 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                   (4 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                   (4 4
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (4 4
                      (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (4 4 (:REWRITE DEFAULT-REALPART))
                   (4 4 (:REWRITE DEFAULT-NUMERATOR))
                   (4 4 (:REWRITE DEFAULT-IMAGPART))
                   (4 4 (:REWRITE DEFAULT-DENOMINATOR))
                   (4 2 (:REWRITE O-INFP-O-FINP-O<=))
                   (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
                   (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (1 1
                      (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::RP-TERMP-OF-EX-FROM-RP/--
     (55966 310
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (55558 214 (:DEFINITION APPLY$-BADGEP))
     (43000 400 (:DEFINITION SUBSETP-EQUAL))
     (35000 3000 (:DEFINITION MEMBER-EQUAL))
     (23900 1000 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (22000 1600
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (20857 20821 (:REWRITE DEFAULT-CAR))
     (19511 698
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (9960 2706 (:REWRITE O-P-O-INFP-CAR))
     (6000 6000 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (5402 922 (:REWRITE RP::IS-IF-RP-TERMP))
     (5200 5200 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (4800 4800
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (3200 3200
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (2800 2800 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2522 2366 (:REWRITE O-P-DEF-O-FINP-1))
     (1900 200 (:DEFINITION NATP))
     (1760 200
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (1680 100 (:DEFINITION TRUE-LISTP))
     (1521 1521 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1474 1474
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1214 1214 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (1000 1000
           (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (912 214 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (800 400
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (714 714
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (700 700 (:TYPE-PRESCRIPTION LEN))
     (700 100 (:DEFINITION LEN))
     (600 300
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (600 100 (:DEFINITION ALL-NILS))
     (500 500 (:TYPE-PRESCRIPTION ALL-NILS))
     (400 400 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (300 300
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (220 104
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (200 200
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (200 200 (:LINEAR LEN-WHEN-PREFIXP))
     (200 100 (:REWRITE DEFAULT-+-2))
     (200 100
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (156 156 (:TYPE-PRESCRIPTION O-FINP))
     (100 100
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (100 100 (:REWRITE DEFAULT-<-2))
     (100 100 (:REWRITE DEFAULT-<-1))
     (100 100 (:REWRITE DEFAULT-+-1))
     (100 100 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (100 100 (:LINEAR BOUNDS-POSITION-EQUAL))
     (99 11
         (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (72 72
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (10 10
         (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::EX-FROM---$INLINE)
(RP::PP-ORDER$INLINE (1796 1796 (:REWRITE DEFAULT-CDR))
                     (1298 1298 (:REWRITE DEFAULT-CAR))
                     (732 204 (:REWRITE O-P-O-INFP-CAR))
                     (176 176 (:REWRITE O-P-DEF-O-FINP-1))
                     (174 44 (:REWRITE RP::IS-IF-RP-TERMP))
                     (96 16 (:REWRITE RP::NOT-INCLUDE-RP))
                     (90 90 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                     (80 20 (:REWRITE RP::RP-TERMP-CADR))
                     (72 72
                         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                     (64 14 (:DEFINITION RP::INCLUDE-FNC))
                     (40 10
                         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                     (32 2 (:DEFINITION RP::EX-FROM-RP))
                     (22 22
                         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                     (18 18 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                     (14 2 (:REWRITE RP::IFIX-OPENER))
                     (10 2
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                     (6 2 (:DEFINITION APPLY$-BADGEP))
                     (4 4
                        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
                     (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
                     (4 4
                        (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                     (4 4
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (4 2
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
                     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                     (2 2
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (2 2
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::BOOLEANP-OF-PP-ORDER.EQUALS
     (23632 1477 (:DEFINITION RP::EX-FROM-RP))
     (16247 1477 (:REWRITE RP::NOT-INCLUDE-RP))
     (11816 1477 (:DEFINITION RP::INCLUDE-FNC))
     (5992 5692 (:REWRITE DEFAULT-CDR))
     (5463 5163 (:REWRITE DEFAULT-CAR))
     (4431 4431
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2954 2954
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (2954 1477 (:DEFINITION QUOTEP))
     (1477 1477
           (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (1204 226 (:REWRITE O-P-O-INFP-CAR))
     (526 226 (:REWRITE O-P-DEF-O-FINP-1))
     (300 300 (:TYPE-PRESCRIPTION O-FINP))
     (266 38 (:REWRITE RP::IFIX-OPENER))
     (190 38
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (114 38 (:DEFINITION APPLY$-BADGEP))
     (76 38 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (63 63 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (44 22 (:REWRITE O-INFP->NEQ-0))
     (38 38 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (38 38
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 23 (:REWRITE DEFAULT-<-2))
     (24 23 (:REWRITE DEFAULT-<-1)))
(RP::PP-LST-ORDEREDP (5557 19 (:DEFINITION RP::RP-TERMP))
                     (3877 19 (:DEFINITION RP::FALIST-CONSISTENT))
                     (3010 19
                           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                     (2232 2232 (:REWRITE DEFAULT-CDR))
                     (1444 1444 (:REWRITE DEFAULT-CAR))
                     (1313 33
                           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                     (1188 36 (:DEFINITION QUOTEP))
                     (1106 4
                           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                     (1102 2 (:DEFINITION APPLY$-BADGEP))
                     (1075 93 (:REWRITE RP::IS-IF-RP-TERMP))
                     (973 55 (:REWRITE RP::RP-TERMP-CADR))
                     (860 8 (:DEFINITION SUBSETP-EQUAL))
                     (818 233 (:REWRITE O-P-O-INFP-CAR))
                     (700 60 (:DEFINITION MEMBER-EQUAL))
                     (651 33
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                     (478 20 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                     (440 32
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                     (390 390 (:TYPE-PRESCRIPTION O-P))
                     (200 38 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                     (195 195 (:REWRITE O-P-DEF-O-FINP-1))
                     (179 30
                          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                     (169 169
                          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                     (120 120 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                     (115 115
                          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                     (114 38 (:REWRITE RP::RP-TERMP-CADDR))
                     (105 105 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                     (104 104 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                     (96 96
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                     (64 64
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                     (56 56 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                     (42 7 (:REWRITE RP::NOT-INCLUDE-RP))
                     (40 4
                         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                     (38 4 (:DEFINITION NATP))
                     (36 2 (:DEFINITION TRUE-LISTP))
                     (33 33 (:TYPE-PRESCRIPTION QUOTEP))
                     (31 31
                         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                     (30 30
                         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                     (28 7 (:DEFINITION RP::INCLUDE-FNC))
                     (22 22 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                     (20 20
                         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
                     (16 8
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                     (14 14 (:TYPE-PRESCRIPTION LEN))
                     (14 2 (:DEFINITION LEN))
                     (12 6
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                     (12 2 (:DEFINITION ALL-NILS))
                     (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
                     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
                     (8 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
                     (7 7 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                     (6 6
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (4 4
                        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                     (4 2 (:REWRITE DEFAULT-+-2))
                     (4 2
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                     (4 2
                        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                     (2 2 (:REWRITE DEFAULT-<-2))
                     (2 2 (:REWRITE DEFAULT-<-1))
                     (2 2 (:REWRITE DEFAULT-+-1))
                     (2 2 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                     (2 2 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::PP-ORDEREDP (292 1 (:DEFINITION RP::RP-TERMP))
                 (199 1 (:DEFINITION RP::FALIST-CONSISTENT))
                 (154 1
                      (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                 (102 102 (:REWRITE DEFAULT-CDR))
                 (75 75 (:REWRITE DEFAULT-CAR))
                 (42 12 (:REWRITE O-P-O-INFP-CAR))
                 (20 20 (:TYPE-PRESCRIPTION O-P))
                 (16 4 (:REWRITE RP::IS-IF-RP-TERMP))
                 (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                 (9 9 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                 (9 2
                    (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                 (8 2 (:REWRITE RP::RP-TERMP-CADR))
                 (8 2 (:REWRITE RP::RP-TERMP-CADDR))
                 (8 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                 (6 6
                    (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                 (6 1 (:REWRITE RP::NOT-INCLUDE-RP))
                 (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                 (4 1
                    (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                 (4 1 (:DEFINITION RP::INCLUDE-FNC))
                 (2 2
                    (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                 (1 1 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                 (1 1
                    (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::PP-ORDER-AND-NEGATED-TERMSP
     (995 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (770 5
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (531 531 (:REWRITE DEFAULT-CDR))
     (384 384 (:REWRITE DEFAULT-CAR))
     (210 60 (:REWRITE O-P-O-INFP-CAR))
     (88 22 (:REWRITE RP::IS-IF-RP-TERMP))
     (63 9
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (50 50 (:REWRITE O-P-DEF-O-FINP-1))
     (48 12 (:REWRITE RP::RP-TERMP-CADR))
     (45 10
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (40 10 (:REWRITE RP::RP-TERMP-CADDR))
     (40 10 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (36 9
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (34 34
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (30 5 (:REWRITE RP::NOT-INCLUDE-RP))
     (28 14 (:DEFINITION QUOTEP))
     (25 25 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (20 5 (:DEFINITION RP::INCLUDE-FNC))
     (10 10
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 9 (:TYPE-PRESCRIPTION QUOTEP))
     (5 5 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (5 5
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::BOOLEANP-OF-PP-ORDER-AND-NEGATED-TERMSP.NEGATED-TERMS
     (101 101 (:REWRITE DEFAULT-CDR))
     (45 45 (:REWRITE DEFAULT-CAR)))
(RP::BOOLEANP-OF-PP-ORDER-AND-NEGATED-TERMSP.EQUAL-TERMS
     (101 101 (:REWRITE DEFAULT-CDR))
     (45 45 (:REWRITE DEFAULT-CAR)))
(RP::PP-SUM-MERGE-AUX (2412 42
                            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                      (2338 46 (:DEFINITION QUOTEP))
                      (2222 10
                            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                      (2210 6 (:DEFINITION APPLY$-BADGEP))
                      (1720 16 (:DEFINITION SUBSETP-EQUAL))
                      (1718 10 (:DEFINITION RP::RP-TERMP))
                      (1400 120 (:DEFINITION MEMBER-EQUAL))
                      (1302 1242 (:REWRITE DEFAULT-CDR))
                      (1244 42
                            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                      (1226 6 (:DEFINITION RP::FALIST-CONSISTENT))
                      (956 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                      (952 6
                           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                      (880 64
                           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                      (743 703 (:REWRITE DEFAULT-CAR))
                      (356 156 (:REWRITE RP::MEASURE-LEMMA1))
                      (280 10 (:DEFINITION RP::EX-FROM-RP))
                      (261 5 (:REWRITE O<=-O-FINP-DEF))
                      (260 74 (:REWRITE O-P-O-INFP-CAR))
                      (240 240 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                      (208 208 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                      (192 192
                           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                      (142 12 (:REWRITE RP::NOT-INCLUDE-RP))
                      (128 128
                           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                      (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                      (108 12 (:DEFINITION RP::INCLUDE-FNC))
                      (92 30 (:REWRITE RP::IS-IF-RP-TERMP))
                      (84 84
                          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                      (82 54 (:REWRITE RP::CONS-COUNT-ATOM))
                      (80 8
                          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                      (76 8 (:DEFINITION NATP))
                      (72 4 (:DEFINITION TRUE-LISTP))
                      (68 4 (:REWRITE RP::MEASURE-LEMMA6))
                      (56 18 (:REWRITE RP::RP-TERMP-CADR))
                      (54 54 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                      (52 52 (:REWRITE RP::MEASURE-LEMMA1-2))
                      (46 46 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                      (42 42 (:TYPE-PRESCRIPTION QUOTEP))
                      (40 40
                          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
                      (40 8
                          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                      (38 38
                          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                      (36 20 (:REWRITE DEFAULT-<-2))
                      (36 20 (:REWRITE DEFAULT-<-1))
                      (36 12 (:REWRITE RP::RP-TERMP-CADDR))
                      (36 12 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                      (34 17 (:REWRITE DEFAULT-+-2))
                      (32 32 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                      (32 16
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                      (30 17 (:REWRITE DEFAULT-+-1))
                      (28 28 (:TYPE-PRESCRIPTION LEN))
                      (28 28
                          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                      (28 4 (:DEFINITION LEN))
                      (25 5 (:REWRITE AC-<))
                      (24 12
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                      (24 4 (:DEFINITION ALL-NILS))
                      (20 20
                          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                      (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
                      (20 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
                      (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
                      (16 16
                          (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                      (16 16
                          (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                      (15 5 (:REWRITE O-INFP-O-FINP-O<=))
                      (12 12
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (8 8
                         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                      (8 8
                         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                      (8 8 (:LINEAR LEN-WHEN-PREFIXP))
                      (8 4
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                      (8 4
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                      (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
                      (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                      (4 4
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                      (4 4 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                      (4 4 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::RP-TERM-LISTP-OF-PP-SUM-MERGE-AUX
     (13307 241
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (12788 212 (:DEFINITION QUOTEP))
     (12221 55
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (12155 33 (:DEFINITION APPLY$-BADGEP))
     (10997 58 (:DEFINITION RP::RP-TERMP))
     (9460 88 (:DEFINITION SUBSETP-EQUAL))
     (7730 38 (:DEFINITION RP::FALIST-CONSISTENT))
     (7700 660 (:DEFINITION MEMBER-EQUAL))
     (7149 7149 (:REWRITE DEFAULT-CDR))
     (6612 241
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (5999 38
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (5258 220 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (4840 352
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (4054 4054 (:REWRITE DEFAULT-CAR))
     (1664 473 (:REWRITE O-P-O-INFP-CAR))
     (1320 1320 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1144 1144 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1056 1056
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (704 704
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (616 616 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (606 185 (:REWRITE RP::IS-IF-RP-TERMP))
     (555 555
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (440 44
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (418 44 (:DEFINITION NATP))
     (397 397 (:REWRITE O-P-DEF-O-FINP-1))
     (396 22 (:DEFINITION TRUE-LISTP))
     (352 109 (:REWRITE RP::RP-TERMP-CADR))
     (333 333 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (275 55
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (254 76 (:REWRITE RP::RP-TERMP-CADDR))
     (254 76 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (253 253 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (239 239 (:TYPE-PRESCRIPTION QUOTEP))
     (220 220
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (206 206
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (176 88
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (154 154 (:TYPE-PRESCRIPTION LEN))
     (154 22 (:DEFINITION LEN))
     (144 144
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (132 66
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (132 22 (:DEFINITION ALL-NILS))
     (110 110 (:TYPE-PRESCRIPTION ALL-NILS))
     (110 33 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (102 17 (:REWRITE RP::NOT-INCLUDE-RP))
     (88 88 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (68 17 (:DEFINITION RP::INCLUDE-FNC))
     (66 66
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (55 55
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (44 44
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (44 44 (:LINEAR LEN-WHEN-PREFIXP))
     (44 22 (:REWRITE DEFAULT-+-2))
     (44 22
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (44 22
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (22 22 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-<-1))
     (22 22 (:REWRITE DEFAULT-+-1))
     (22 22 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (22 22 (:LINEAR BOUNDS-POSITION-EQUAL))
     (17 17
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC)))
(RP::PP-SUM-MERGE (584 2 (:DEFINITION RP::RP-TERMP))
                  (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
                  (308 2
                       (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                  (204 204 (:REWRITE DEFAULT-CDR))
                  (161 161 (:REWRITE DEFAULT-CAR))
                  (84 24 (:REWRITE O-P-O-INFP-CAR))
                  (40 40 (:TYPE-PRESCRIPTION O-P))
                  (32 8 (:REWRITE RP::IS-IF-RP-TERMP))
                  (20 20
                      (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                  (20 20 (:REWRITE O-P-DEF-O-FINP-1))
                  (18 4
                      (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                  (16 4 (:REWRITE RP::RP-TERMP-CADR))
                  (16 4 (:REWRITE RP::RP-TERMP-CADDR))
                  (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                  (12 12
                      (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                  (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
                  (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                  (8 2
                     (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                  (8 2 (:DEFINITION RP::INCLUDE-FNC))
                  (4 4
                     (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                  (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                  (2 2
                     (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-PP-SUM-MERGE
     (1791 9 (:DEFINITION RP::FALIST-CONSISTENT))
     (1386 9
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (935 935 (:REWRITE DEFAULT-CDR))
     (704 704 (:REWRITE DEFAULT-CAR))
     (378 108 (:REWRITE O-P-O-INFP-CAR))
     (152 38 (:REWRITE RP::IS-IF-RP-TERMP))
     (111 15
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (90 90 (:REWRITE O-P-DEF-O-FINP-1))
     (89 20
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (80 20 (:REWRITE RP::RP-TERMP-CADR))
     (72 18 (:REWRITE RP::RP-TERMP-CADDR))
     (72 18 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (60 24 (:DEFINITION QUOTEP))
     (60 15
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (58 58
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (54 9 (:REWRITE RP::NOT-INCLUDE-RP))
     (47 47 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (36 9 (:DEFINITION RP::INCLUDE-FNC))
     (20 20
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (15 15 (:TYPE-PRESCRIPTION QUOTEP))
     (10 2
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (9 9 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (9 9
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (6 2 (:DEFINITION APPLY$-BADGEP))
     (5 5 (:TYPE-PRESCRIPTION RP::PP-SUM-MERGE))
     (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (3 3
        (:TYPE-PRESCRIPTION RP::CREATE-LIST-INSTANCE))
     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::S-ORDER-AND-NEGATED-TERMSP
     (995 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (770 5
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (531 531 (:REWRITE DEFAULT-CDR))
     (384 384 (:REWRITE DEFAULT-CAR))
     (210 60 (:REWRITE O-P-O-INFP-CAR))
     (88 22 (:REWRITE RP::IS-IF-RP-TERMP))
     (63 9
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (50 50 (:REWRITE O-P-DEF-O-FINP-1))
     (48 12 (:REWRITE RP::RP-TERMP-CADR))
     (45 10
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (40 10 (:REWRITE RP::RP-TERMP-CADDR))
     (40 10 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (36 9
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (34 34
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (30 5 (:REWRITE RP::NOT-INCLUDE-RP))
     (28 14 (:DEFINITION QUOTEP))
     (25 25 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (20 5 (:DEFINITION RP::INCLUDE-FNC))
     (10 10
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (9 9 (:TYPE-PRESCRIPTION QUOTEP))
     (5 5 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (5 5
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::S-SUM-MERGE-AUX (2412 42
                           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                     (2338 46 (:DEFINITION QUOTEP))
                     (2222 10
                           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                     (2210 6 (:DEFINITION APPLY$-BADGEP))
                     (1720 16 (:DEFINITION SUBSETP-EQUAL))
                     (1718 10 (:DEFINITION RP::RP-TERMP))
                     (1400 120 (:DEFINITION MEMBER-EQUAL))
                     (1302 1242 (:REWRITE DEFAULT-CDR))
                     (1244 42
                           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                     (1226 6 (:DEFINITION RP::FALIST-CONSISTENT))
                     (956 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                     (952 6
                          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                     (880 64
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                     (743 703 (:REWRITE DEFAULT-CAR))
                     (356 156 (:REWRITE RP::MEASURE-LEMMA1))
                     (280 10 (:DEFINITION RP::EX-FROM-RP))
                     (261 5 (:REWRITE O<=-O-FINP-DEF))
                     (260 74 (:REWRITE O-P-O-INFP-CAR))
                     (240 240 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                     (208 208 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                     (192 192
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                     (142 12 (:REWRITE RP::NOT-INCLUDE-RP))
                     (128 128
                          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                     (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                     (108 12 (:DEFINITION RP::INCLUDE-FNC))
                     (92 30 (:REWRITE RP::IS-IF-RP-TERMP))
                     (84 84
                         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                     (82 54 (:REWRITE RP::CONS-COUNT-ATOM))
                     (80 8
                         (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                     (76 8 (:DEFINITION NATP))
                     (72 4 (:DEFINITION TRUE-LISTP))
                     (68 4 (:REWRITE RP::MEASURE-LEMMA6))
                     (56 18 (:REWRITE RP::RP-TERMP-CADR))
                     (54 54 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                     (52 52 (:REWRITE RP::MEASURE-LEMMA1-2))
                     (46 46 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                     (42 42 (:TYPE-PRESCRIPTION QUOTEP))
                     (40 40
                         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
                     (40 8
                         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                     (38 38
                         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                     (36 20 (:REWRITE DEFAULT-<-2))
                     (36 20 (:REWRITE DEFAULT-<-1))
                     (36 12 (:REWRITE RP::RP-TERMP-CADDR))
                     (36 12 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                     (34 17 (:REWRITE DEFAULT-+-2))
                     (32 32 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                     (32 16
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                     (30 17 (:REWRITE DEFAULT-+-1))
                     (28 28 (:TYPE-PRESCRIPTION LEN))
                     (28 4 (:DEFINITION LEN))
                     (25 5 (:REWRITE AC-<))
                     (24 12
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                     (24 4 (:DEFINITION ALL-NILS))
                     (20 20
                         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                     (20 20
                         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                     (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
                     (20 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
                     (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
                     (16 16
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
                     (16 16
                         (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
                     (15 5 (:REWRITE O-INFP-O-FINP-O<=))
                     (12 12
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (8 8
                        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                     (8 8
                        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
                     (8 4
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                     (8 4
                        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                     (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
                     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                     (4 4
                        (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
                     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                     (4 4 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::RP-TERM-LISTP-OF-S-SUM-MERGE-AUX
     (13307 241
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (12788 212 (:DEFINITION QUOTEP))
     (12221 55
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (12155 33 (:DEFINITION APPLY$-BADGEP))
     (10997 58 (:DEFINITION RP::RP-TERMP))
     (9460 88 (:DEFINITION SUBSETP-EQUAL))
     (7730 38 (:DEFINITION RP::FALIST-CONSISTENT))
     (7700 660 (:DEFINITION MEMBER-EQUAL))
     (7149 7149 (:REWRITE DEFAULT-CDR))
     (6612 241
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (5999 38
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (5258 220 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (4840 352
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (4054 4054 (:REWRITE DEFAULT-CAR))
     (1664 473 (:REWRITE O-P-O-INFP-CAR))
     (1320 1320 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1144 1144 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1056 1056
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (704 704
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (616 616 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (606 185 (:REWRITE RP::IS-IF-RP-TERMP))
     (555 555
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (440 44
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (418 44 (:DEFINITION NATP))
     (397 397 (:REWRITE O-P-DEF-O-FINP-1))
     (396 22 (:DEFINITION TRUE-LISTP))
     (352 109 (:REWRITE RP::RP-TERMP-CADR))
     (333 333 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (275 55
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (254 76 (:REWRITE RP::RP-TERMP-CADDR))
     (254 76 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (253 253 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (239 239 (:TYPE-PRESCRIPTION QUOTEP))
     (220 220
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (206 206
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (176 88
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (154 154 (:TYPE-PRESCRIPTION LEN))
     (154 22 (:DEFINITION LEN))
     (132 132
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (132 66
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (132 22 (:DEFINITION ALL-NILS))
     (110 110 (:TYPE-PRESCRIPTION ALL-NILS))
     (110 33 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (102 17 (:REWRITE RP::NOT-INCLUDE-RP))
     (88 88 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (68 17 (:DEFINITION RP::INCLUDE-FNC))
     (66 66
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (55 55
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (44 44
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (44 44 (:LINEAR LEN-WHEN-PREFIXP))
     (44 22 (:REWRITE DEFAULT-+-2))
     (44 22
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (44 22
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (22 22 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (22 22 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-<-1))
     (22 22 (:REWRITE DEFAULT-+-1))
     (22 22 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (22 22 (:LINEAR BOUNDS-POSITION-EQUAL))
     (17 17
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC)))
(RP::S-SUM-MERGE (584 2 (:DEFINITION RP::RP-TERMP))
                 (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
                 (308 2
                      (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                 (204 204 (:REWRITE DEFAULT-CDR))
                 (161 161 (:REWRITE DEFAULT-CAR))
                 (84 24 (:REWRITE O-P-O-INFP-CAR))
                 (40 40 (:TYPE-PRESCRIPTION O-P))
                 (32 8 (:REWRITE RP::IS-IF-RP-TERMP))
                 (20 20
                     (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                 (20 20 (:REWRITE O-P-DEF-O-FINP-1))
                 (18 4
                     (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                 (16 4 (:REWRITE RP::RP-TERMP-CADR))
                 (16 4 (:REWRITE RP::RP-TERMP-CADDR))
                 (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                 (12 12
                     (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                 (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
                 (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                 (8 2
                    (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                 (8 2 (:DEFINITION RP::INCLUDE-FNC))
                 (4 4
                    (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                 (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                 (2 2
                    (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-S-SUM-MERGE
     (1791 9 (:DEFINITION RP::FALIST-CONSISTENT))
     (1386 9
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (931 931 (:REWRITE DEFAULT-CDR))
     (704 704 (:REWRITE DEFAULT-CAR))
     (378 108 (:REWRITE O-P-O-INFP-CAR))
     (152 38 (:REWRITE RP::IS-IF-RP-TERMP))
     (111 15
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (90 90 (:REWRITE O-P-DEF-O-FINP-1))
     (89 20
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (80 20 (:REWRITE RP::RP-TERMP-CADR))
     (72 18 (:REWRITE RP::RP-TERMP-CADDR))
     (72 18 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (60 24 (:DEFINITION QUOTEP))
     (60 15
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (58 58
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (54 9 (:REWRITE RP::NOT-INCLUDE-RP))
     (47 47 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (36 9 (:DEFINITION RP::INCLUDE-FNC))
     (20 20
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (15 15 (:TYPE-PRESCRIPTION QUOTEP))
     (10 2
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (9 9 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (9 9
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (6 2 (:DEFINITION APPLY$-BADGEP))
     (5 5 (:TYPE-PRESCRIPTION RP::S-SUM-MERGE))
     (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (3 3
        (:TYPE-PRESCRIPTION RP::CREATE-LIST-INSTANCE))
     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::S-FIX-PP-ARGS-AUX
     (5268 8 (:DEFINITION APPLY$-BADGEP))
     (4482 47
           (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (4448 58 (:DEFINITION QUOTEP))
     (3760 20
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3472 32 (:DEFINITION SUBSETP-EQUAL))
     (3248 15 (:DEFINITION RP::RP-TERMP))
     (2832 240 (:DEFINITION MEMBER-EQUAL))
     (2601 2493 (:REWRITE DEFAULT-CDR))
     (2248 12 (:DEFINITION RP::FALIST-CONSISTENT))
     (2166 47
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1926 80 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (1780 128
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1743 11
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1335 1335 (:REWRITE DEFAULT-CAR))
     (1023 24
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (970 16
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (843 8 (:DEFINITION TRUE-LISTP))
     (686 188 (:REWRITE O-P-O-INFP-CAR))
     (650 10 (:DEFINITION RP::RP-EQUAL))
     (579 11
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (576 24 (:DEFINITION RP::EX-FROM-RP))
     (480 480 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (416 416 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (384 384
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (384 28 (:REWRITE RP::NOT-INCLUDE-RP))
     (304 28 (:DEFINITION RP::INCLUDE-FNC))
     (256 256
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (250 10 (:REWRITE RP::EX-FROM-RP-X2))
     (224 224 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (224 68 (:REWRITE RP::IS-IF-RP-TERMP))
     (166 166 (:REWRITE O-P-DEF-O-FINP-1))
     (158 16 (:DEFINITION NATP))
     (133 133
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (106 49 (:REWRITE DEFAULT-+-2))
     (100 12 (:DEFINITION LEN))
     (99 99 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (96 31 (:REWRITE RP::RP-TERMP-CADR))
     (94 94 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (88 27 (:REWRITE RP::RP-TERMP-CADDR))
     (88 27 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (85 17
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (80 80
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (76 76 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (67 67
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (65 49 (:REWRITE DEFAULT-+-1))
     (64 32
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (60 60 (:TYPE-PRESCRIPTION LEN))
     (60 4 (:DEFINITION LENGTH))
     (48 48
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (48 8 (:DEFINITION ALL-NILS))
     (47 47 (:TYPE-PRESCRIPTION QUOTEP))
     (40 40 (:TYPE-PRESCRIPTION ALL-NILS))
     (40 10 (:REWRITE RP::RP-TERMP-CADDDR))
     (37 1 (:REWRITE O<=-O-FINP-DEF))
     (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (32 8 (:REWRITE COMMUTATIVITY-OF-+))
     (32 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (32 8 (:DEFINITION INTEGER-ABS))
     (27 27
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 6 (:REWRITE RP::RP-TERMP-CADDDDR))
     (23 11
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (21 18 (:REWRITE DEFAULT-<-2))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (19 18 (:REWRITE DEFAULT-<-1))
     (17 17
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (16 16
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (12 12
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (12 12 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (12 8 (:REWRITE STR::CONSP-OF-EXPLODE))
     (10 10
         (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (10 10 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
     (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 4
        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (5 5
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (5 1 (:REWRITE AC-<))
     (4 4
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (4 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (4 4
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (4 4 (:REWRITE DEFAULT-REALPART))
     (4 4 (:REWRITE DEFAULT-NUMERATOR))
     (4 4 (:REWRITE DEFAULT-IMAGPART))
     (4 4 (:REWRITE DEFAULT-DENOMINATOR))
     (4 4
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (3 3 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (2 2
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (2 2
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (2 1 (:REWRITE O-INFP-O-FINP-O<=))
     (1 1
        (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::RP-TERM-LISTP-OF-S-FIX-PP-ARGS-AUX
     (43354 169 (:DEFINITION RP::RP-TERMP))
     (36299 561
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (33572 58 (:DEFINITION APPLY$-BADGEP))
     (30911 114
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (29196 164 (:DEFINITION RP::FALIST-CONSISTENT))
     (25417 24389 (:REWRITE DEFAULT-CDR))
     (24670 228 (:DEFINITION SUBSETP-EQUAL))
     (22596 144
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (20110 1710 (:DEFINITION MEMBER-EQUAL))
     (17208 561
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (13693 570 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (12640 912
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (8600 2343 (:REWRITE O-P-O-INFP-CAR))
     (5980 246 (:DEFINITION RP::EX-FROM-RP))
     (4232 330 (:REWRITE RP::NOT-INCLUDE-RP))
     (3583 721 (:REWRITE RP::IS-IF-RP-TERMP))
     (3420 3420 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (3326 330 (:DEFINITION RP::INCLUDE-FNC))
     (3085 114
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (2964 2964 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (2899 57
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2736 2736
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (2731 57 (:DEFINITION TRUE-LISTP))
     (2147 2055 (:REWRITE O-P-DEF-O-FINP-1))
     (2031 2031
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1824 1824
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1596 1596 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1376 268
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1212 303 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (1164 303 (:REWRITE RP::RP-TERMP-CADDR))
     (1113 114 (:DEFINITION NATP))
     (1066 1066 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (822 822
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (645 645 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (624 624
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (572 572
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (570 570
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (492 492
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (456 228
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (399 399 (:TYPE-PRESCRIPTION LEN))
     (399 57 (:DEFINITION LEN))
     (342 171
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (342 57 (:DEFINITION ALL-NILS))
     (285 285 (:TYPE-PRESCRIPTION ALL-NILS))
     (268 268
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (232 58 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (228 228 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (171 171
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (154 72
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (124 124 (:LINEAR LEN-WHEN-PREFIXP))
     (120 30 (:REWRITE RP::RP-TERMP-CADDDR))
     (114 114
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (114 57 (:REWRITE DEFAULT-+-2))
     (92 92 (:TYPE-PRESCRIPTION O-FINP))
     (62 62 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (62 62 (:LINEAR BOUNDS-POSITION-EQUAL))
     (60 15 (:REWRITE RP::RP-TERMP-CADDDDR))
     (57 57 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (57 57 (:REWRITE DEFAULT-<-2))
     (57 57 (:REWRITE DEFAULT-<-1))
     (57 57 (:REWRITE DEFAULT-+-1))
     (30 30
         (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (24 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::S-FIX-ARGS (292 1 (:DEFINITION RP::RP-TERMP))
                (199 1 (:DEFINITION RP::FALIST-CONSISTENT))
                (154 1
                     (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                (102 102 (:REWRITE DEFAULT-CDR))
                (76 76 (:REWRITE DEFAULT-CAR))
                (42 12 (:REWRITE O-P-O-INFP-CAR))
                (20 20 (:TYPE-PRESCRIPTION O-P))
                (16 4 (:REWRITE RP::IS-IF-RP-TERMP))
                (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                (9 9 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                (9 2
                   (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                (8 2 (:REWRITE RP::RP-TERMP-CADR))
                (8 2 (:REWRITE RP::RP-TERMP-CADDR))
                (8 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                (6 6
                   (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                (6 1 (:REWRITE RP::NOT-INCLUDE-RP))
                (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                (4 1
                   (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                (4 1 (:DEFINITION RP::INCLUDE-FNC))
                (2 2
                   (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                (1 1 (:TYPE-PRESCRIPTION RP::S-FIX-ARGS))
                (1 1 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                (1 1
                   (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-S-FIX-ARGS
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (209 209 (:REWRITE DEFAULT-CDR))
     (161 161 (:REWRITE DEFAULT-CAR))
     (84 24 (:REWRITE O-P-O-INFP-CAR))
     (38 5
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (28 1 (:DEFINITION RP::RP-TERM-LISTP))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (20 7 (:DEFINITION QUOTEP))
     (20 5
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (20 5 (:REWRITE RP::RP-TERMP-CADR))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 14
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (5 5 (:TYPE-PRESCRIPTION RP::S-FIX-ARGS))
     (5 5 (:TYPE-PRESCRIPTION QUOTEP))
     (5 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (3 1 (:DEFINITION APPLY$-BADGEP))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1 1 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::C-FIX-ARG-AUX (5268 8 (:DEFINITION APPLY$-BADGEP))
                   (4482 47
                         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                   (4456 62 (:DEFINITION QUOTEP))
                   (3760 20
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (3472 32 (:DEFINITION SUBSETP-EQUAL))
                   (3248 15 (:DEFINITION RP::RP-TERMP))
                   (2832 240 (:DEFINITION MEMBER-EQUAL))
                   (2643 2519 (:REWRITE DEFAULT-CDR))
                   (2248 12 (:DEFINITION RP::FALIST-CONSISTENT))
                   (2166 47
                         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (1926 80 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
                   (1780 128
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (1743 11
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (1365 1365 (:REWRITE DEFAULT-CAR))
                   (1023 24
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (970 16
                        (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
                   (843 8 (:DEFINITION TRUE-LISTP))
                   (780 12 (:DEFINITION RP::RP-EQUAL))
                   (718 196 (:REWRITE O-P-O-INFP-CAR))
                   (672 28 (:DEFINITION RP::EX-FROM-RP))
                   (579 11
                        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (480 480 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (444 32 (:REWRITE RP::NOT-INCLUDE-RP))
                   (416 416 (:REWRITE SUBSETP-IMPLIES-MEMBER))
                   (384 384
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (352 32 (:DEFINITION RP::INCLUDE-FNC))
                   (300 12 (:REWRITE RP::EX-FROM-RP-X2))
                   (256 256
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (224 224 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (224 68 (:REWRITE RP::IS-IF-RP-TERMP))
                   (174 174 (:REWRITE O-P-DEF-O-FINP-1))
                   (158 16 (:DEFINITION NATP))
                   (133 133
                        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (106 49 (:REWRITE DEFAULT-+-2))
                   (100 12 (:DEFINITION LEN))
                   (99 99 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (98 98 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (96 31 (:REWRITE RP::RP-TERMP-CADR))
                   (88 88 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                   (88 27 (:REWRITE RP::RP-TERMP-CADDR))
                   (88 27 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (85 17
                       (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (80 80
                       (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
                   (67 67
                       (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                   (65 49 (:REWRITE DEFAULT-+-1))
                   (64 32
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (60 60 (:TYPE-PRESCRIPTION LEN))
                   (60 4 (:DEFINITION LENGTH))
                   (56 56
                       (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                   (48 8 (:DEFINITION ALL-NILS))
                   (47 47 (:TYPE-PRESCRIPTION QUOTEP))
                   (40 40 (:TYPE-PRESCRIPTION ALL-NILS))
                   (40 10 (:REWRITE RP::RP-TERMP-CADDDR))
                   (37 1 (:REWRITE O<=-O-FINP-DEF))
                   (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
                   (32 8 (:REWRITE COMMUTATIVITY-OF-+))
                   (32 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (32 8 (:DEFINITION INTEGER-ABS))
                   (27 27
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (24 6 (:REWRITE RP::RP-TERMP-CADDDDR))
                   (23 11
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (21 18 (:REWRITE DEFAULT-<-2))
                   (20 20 (:LINEAR LEN-WHEN-PREFIXP))
                   (19 18 (:REWRITE DEFAULT-<-1))
                   (17 17
                       (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                   (16 16
                       (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                   (12 12
                       (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                   (12 12
                       (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
                   (12 12 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
                   (12 12 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (12 8 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
                   (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
                   (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
                   (8 4
                      (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                   (5 5
                      (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                   (5 1 (:REWRITE AC-<))
                   (4 4 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                   (4 4
                      (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (4 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                   (4 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                   (4 4
                      (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (4 4 (:REWRITE DEFAULT-REALPART))
                   (4 4 (:REWRITE DEFAULT-NUMERATOR))
                   (4 4 (:REWRITE DEFAULT-IMAGPART))
                   (4 4 (:REWRITE DEFAULT-DENOMINATOR))
                   (4 4
                      (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                   (2 2
                      (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                   (2 2
                      (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                   (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                   (1 1
                      (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::RP-TERM-LISTP-OF-C-FIX-ARG-AUX.COUGHED-LST
     (49068 191 (:DEFINITION RP::RP-TERMP))
     (40541 675
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (39695 905 (:DEFINITION QUOTEP))
     (37429 65 (:DEFINITION APPLY$-BADGEP))
     (34782 128
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (33042 186 (:DEFINITION RP::FALIST-CONSISTENT))
     (28741 27587 (:REWRITE DEFAULT-CDR))
     (27680 256 (:DEFINITION SUBSETP-EQUAL))
     (25571 163
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (22560 1920 (:DEFINITION MEMBER-EQUAL))
     (19665 675
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (15366 640 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (14180 1024
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (9722 2648 (:REWRITE O-P-O-INFP-CAR))
     (6740 277 (:DEFINITION RP::EX-FROM-RP))
     (4777 373 (:REWRITE RP::NOT-INCLUDE-RP))
     (3868 801 (:REWRITE RP::IS-IF-RP-TERMP))
     (3840 3840 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (3754 373 (:DEFINITION RP::INCLUDE-FNC))
     (3328 3328 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (3225 128
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (3072 3072
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (2913 64
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2857 64 (:DEFINITION TRUE-LISTP))
     (2460 430 (:REWRITE RP::RP-TERMP-CADR))
     (2430 2322 (:REWRITE O-P-DEF-O-FINP-1))
     (2322 2322
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (2048 2048
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1792 1792 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1561 305
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1360 341 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (1312 341 (:REWRITE RP::RP-TERMP-CADDR))
     (1254 1254 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1246 128 (:DEFINITION NATP))
     (927 927
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (722 722 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (699 699
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (692 692
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (675 675 (:TYPE-PRESCRIPTION QUOTEP))
     (640 640
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (554 554
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (512 256
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (448 448 (:TYPE-PRESCRIPTION LEN))
     (448 64 (:DEFINITION LEN))
     (384 192
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (384 64 (:DEFINITION ALL-NILS))
     (320 320 (:TYPE-PRESCRIPTION ALL-NILS))
     (305 305
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (260 65 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (256 256 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (192 192
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (168 79
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (138 138 (:LINEAR LEN-WHEN-PREFIXP))
     (128 128
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (128 64 (:REWRITE DEFAULT-+-2))
     (120 30 (:REWRITE RP::RP-TERMP-CADDDR))
     (108 108 (:TYPE-PRESCRIPTION O-FINP))
     (69 69 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (69 69 (:LINEAR BOUNDS-POSITION-EQUAL))
     (64 64 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (64 64 (:REWRITE DEFAULT-<-2))
     (64 64 (:REWRITE DEFAULT-<-1))
     (64 64 (:REWRITE DEFAULT-+-1))
     (60 15 (:REWRITE RP::RP-TERMP-CADDDDR))
     (36 36
         (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE)))
(RP::RP-TERM-LISTP-OF-C-FIX-ARG-AUX.CLEANED-LST
     (60073 229 (:DEFINITION RP::RP-TERMP))
     (46527 770
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (42939 75 (:DEFINITION APPLY$-BADGEP))
     (40488 224 (:DEFINITION RP::FALIST-CONSISTENT))
     (40312 148
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (34446 33084 (:REWRITE DEFAULT-CDR))
     (31980 296 (:DEFINITION SUBSETP-EQUAL))
     (31339 200
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (26060 2220 (:DEFINITION MEMBER-EQUAL))
     (22782 770
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (17756 740 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (16380 1184
            (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (11820 3228 (:REWRITE O-P-O-INFP-CAR))
     (7988 329 (:DEFINITION RP::EX-FROM-RP))
     (5719 452 (:REWRITE RP::NOT-INCLUDE-RP))
     (4489 962 (:REWRITE RP::IS-IF-RP-TERMP))
     (4486 452 (:DEFINITION RP::INCLUDE-FNC))
     (4440 4440 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (3848 3848 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (3552 3552
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (3425 148
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (3037 74 (:DEFINITION TRUE-LISTP))
     (2936 2828 (:REWRITE O-P-DEF-O-FINP-1))
     (2933 74
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2880 2880
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (2368 2368
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (2072 2072 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1891 371
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1670 415 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (1622 415 (:REWRITE RP::RP-TERMP-CADDR))
     (1489 1489 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1436 148 (:DEFINITION NATP))
     (1110 1110
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (889 889
          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (832 832 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (816 816
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (740 740
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (658 658
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (592 296
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (518 518 (:TYPE-PRESCRIPTION LEN))
     (518 74 (:DEFINITION LEN))
     (444 222
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (444 74 (:DEFINITION ALL-NILS))
     (371 371
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (370 370 (:TYPE-PRESCRIPTION ALL-NILS))
     (300 75 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (296 296 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (222 222
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (188 89
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (158 158 (:LINEAR LEN-WHEN-PREFIXP))
     (148 148
          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (148 74 (:REWRITE DEFAULT-+-2))
     (120 30 (:REWRITE RP::RP-TERMP-CADDDR))
     (108 108 (:TYPE-PRESCRIPTION O-FINP))
     (79 79 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (79 79 (:LINEAR BOUNDS-POSITION-EQUAL))
     (74 74 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (74 74 (:REWRITE DEFAULT-<-2))
     (74 74 (:REWRITE DEFAULT-<-1))
     (74 74 (:REWRITE DEFAULT-+-1))
     (60 15 (:REWRITE RP::RP-TERMP-CADDDDR))
     (42 42
         (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (24 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::C-FIX-ARG-AUX-WITH-COND$INLINE)
(RP::RP-TERM-LISTP-OF-C-FIX-ARG-AUX-WITH-COND.COUGHED-LST
     (28 2 (:DEFINITION RP::RP-TERM-LISTP))
     (10 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (8 8 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (8 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6 2 (:DEFINITION QUOTEP))
     (4 4 (:REWRITE DEFAULT-CAR))
     (2 2 (:TYPE-PRESCRIPTION QUOTEP))
     (2 2
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2 (:REWRITE DEFAULT-CDR)))
(RP::RP-TERM-LISTP-OF-C-FIX-ARG-AUX-WITH-COND.CLEANED-LST
     (28 2 (:DEFINITION RP::RP-TERM-LISTP))
     (10 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (8 8 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (8 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6 2 (:DEFINITION QUOTEP))
     (4 4 (:REWRITE DEFAULT-CAR))
     (2 2 (:TYPE-PRESCRIPTION QUOTEP))
     (2 2
        (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2 (:REWRITE DEFAULT-CDR)))
(RP::C-FIX-PP-ARGS (292 1 (:DEFINITION RP::RP-TERMP))
                   (199 1 (:DEFINITION RP::FALIST-CONSISTENT))
                   (154 1
                        (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (102 102 (:REWRITE DEFAULT-CDR))
                   (76 76 (:REWRITE DEFAULT-CAR))
                   (42 12 (:REWRITE O-P-O-INFP-CAR))
                   (20 20 (:TYPE-PRESCRIPTION O-P))
                   (16 4 (:REWRITE RP::IS-IF-RP-TERMP))
                   (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                   (9 9 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                   (9 2
                      (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (8 2 (:REWRITE RP::RP-TERMP-CADR))
                   (8 2 (:REWRITE RP::RP-TERMP-CADDR))
                   (8 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                   (6 6
                      (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                   (6 1 (:REWRITE RP::NOT-INCLUDE-RP))
                   (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (4 1
                      (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                   (4 1 (:DEFINITION RP::INCLUDE-FNC))
                   (2 2
                      (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                   (1 1 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                   (1 1
                      (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-C-FIX-PP-ARGS.COUGHED-PP
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (208 208 (:REWRITE DEFAULT-CDR))
     (157 157 (:REWRITE DEFAULT-CAR))
     (84 24 (:REWRITE O-P-O-INFP-CAR))
     (38 5
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (28 1 (:DEFINITION RP::RP-TERM-LISTP))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (20 7 (:DEFINITION QUOTEP))
     (20 5
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (20 5 (:REWRITE RP::RP-TERMP-CADR))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 14
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (5 5 (:TYPE-PRESCRIPTION QUOTEP))
     (5 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (3 1 (:DEFINITION APPLY$-BADGEP))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1 1 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::RP-TERMP-OF-C-FIX-PP-ARGS.CLEANED-PP
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (210 210 (:REWRITE DEFAULT-CDR))
     (162 162 (:REWRITE DEFAULT-CAR))
     (84 24 (:REWRITE O-P-O-INFP-CAR))
     (38 5
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (28 1 (:DEFINITION RP::RP-TERM-LISTP))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (20 7 (:DEFINITION QUOTEP))
     (20 5
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (20 5 (:REWRITE RP::RP-TERMP-CADR))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 14
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (5 5 (:TYPE-PRESCRIPTION QUOTEP))
     (5 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (3 1 (:DEFINITION APPLY$-BADGEP))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1 1 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::C/D-REMOVE-REPEATED-S)
(RP::RETURN-T)
(RP::RETURN-NIL)
(RP::C-FIX-S-ARGS (292 1 (:DEFINITION RP::RP-TERMP))
                  (199 1 (:DEFINITION RP::FALIST-CONSISTENT))
                  (154 1
                       (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                  (102 102 (:REWRITE DEFAULT-CDR))
                  (76 76 (:REWRITE DEFAULT-CAR))
                  (42 12 (:REWRITE O-P-O-INFP-CAR))
                  (20 20 (:TYPE-PRESCRIPTION O-P))
                  (16 4 (:REWRITE RP::IS-IF-RP-TERMP))
                  (10 10 (:REWRITE O-P-DEF-O-FINP-1))
                  (9 9 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
                  (9 2
                     (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                  (8 2 (:REWRITE RP::RP-TERMP-CADR))
                  (8 2 (:REWRITE RP::RP-TERMP-CADDR))
                  (8 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
                  (6 6
                     (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
                  (6 1 (:REWRITE RP::NOT-INCLUDE-RP))
                  (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                  (4 1
                     (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                  (4 1 (:DEFINITION RP::INCLUDE-FNC))
                  (2 2
                     (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                  (1 1 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                  (1 1
                     (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-OF-C-FIX-S-ARGS.COUGHED-S
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (208 208 (:REWRITE DEFAULT-CDR))
     (157 157 (:REWRITE DEFAULT-CAR))
     (84 24 (:REWRITE O-P-O-INFP-CAR))
     (38 5
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (28 1 (:DEFINITION RP::RP-TERM-LISTP))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (20 7 (:DEFINITION QUOTEP))
     (20 5
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (20 5 (:REWRITE RP::RP-TERMP-CADR))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 14
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (5 5 (:TYPE-PRESCRIPTION QUOTEP))
     (5 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (3 1 (:DEFINITION APPLY$-BADGEP))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1 1 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::RP-TERMP-OF-C-FIX-S-ARGS.CLEANED-S
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (210 210 (:REWRITE DEFAULT-CDR))
     (162 162 (:REWRITE DEFAULT-CAR))
     (84 24 (:REWRITE O-P-O-INFP-CAR))
     (38 5
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (36 9 (:REWRITE RP::IS-IF-RP-TERMP))
     (28 1 (:DEFINITION RP::RP-TERM-LISTP))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (20 7 (:DEFINITION QUOTEP))
     (20 5
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (20 5 (:REWRITE RP::RP-TERMP-CADR))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 14
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (5 5 (:TYPE-PRESCRIPTION QUOTEP))
     (5 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (3 1 (:DEFINITION APPLY$-BADGEP))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1 1 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
