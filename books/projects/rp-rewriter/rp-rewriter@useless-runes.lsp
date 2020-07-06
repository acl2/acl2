(RP::REMOVE-RP-FROM-BINDINGS (20 5 (:REWRITE O-P-O-INFP-CAR))
                             (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                             (5 5 (:REWRITE DEFAULT-CAR))
                             (4 4 (:REWRITE DEFAULT-CDR)))
(RP::QUOTE-LISTP)
(RP::RP-APPLY-BINDINGS)
(RP::RP-MATCH-LHS (79 38 (:REWRITE DEFAULT-+-2))
                  (64 2 (:REWRITE O<=-O-FINP-DEF))
                  (60 4 (:DEFINITION LENGTH))
                  (53 38 (:REWRITE DEFAULT-+-1))
                  (44 4 (:DEFINITION LEN))
                  (32 8 (:REWRITE COMMUTATIVITY-OF-+))
                  (32 8 (:DEFINITION INTEGER-ABS))
                  (24 12 (:REWRITE DEFAULT-CDR))
                  (15 15
                      (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                  (15 11 (:REWRITE DEFAULT-<-2))
                  (14 11 (:REWRITE DEFAULT-<-1))
                  (12 12
                      (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                  (12 8 (:REWRITE STR::CONSP-OF-EXPLODE))
                  (11 11 (:REWRITE FOLD-CONSTS-IN-+))
                  (11 11
                      (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                  (10 10 (:REWRITE DEFAULT-CAR))
                  (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
                  (8 8
                     (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                  (8 4
                     (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                  (8 2 (:REWRITE O-P-O-INFP-CAR))
                  (7 7
                     (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                  (7 2 (:REWRITE AC-<))
                  (6 1 (:REWRITE O-FIRST-EXPT-<))
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
                  (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                  (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
                  (2 2 (:REWRITE O-P-DEF-O-FINP-1))
                  (2 1 (:REWRITE O-FIRST-COEFF-<)))
(RP::RP-DOES-LHS-MATCH (219 1 (:DEFINITION RP::RP-TERMP))
                       (199 1 (:DEFINITION RP::FALIST-CONSISTENT))
                       (154 1
                            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                       (147 135 (:REWRITE DEFAULT-CDR))
                       (100 100 (:REWRITE DEFAULT-CAR))
                       (79 38 (:REWRITE DEFAULT-+-2))
                       (64 2 (:REWRITE O<=-O-FINP-DEF))
                       (60 4 (:DEFINITION LENGTH))
                       (54 15 (:REWRITE O-P-O-INFP-CAR))
                       (53 38 (:REWRITE DEFAULT-+-1))
                       (44 4 (:DEFINITION LEN))
                       (32 8 (:REWRITE COMMUTATIVITY-OF-+))
                       (32 8 (:DEFINITION INTEGER-ABS))
                       (15 15
                           (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                       (15 11 (:REWRITE DEFAULT-<-2))
                       (14 11 (:REWRITE DEFAULT-<-1))
                       (13 13 (:REWRITE O-P-DEF-O-FINP-1))
                       (12 12
                           (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                       (12 8 (:REWRITE STR::CONSP-OF-EXPLODE))
                       (11 11 (:REWRITE FOLD-CONSTS-IN-+))
                       (11 11
                           (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                       (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
                       (8 8
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                       (8 4
                          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                       (7 7 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                       (7 7
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                       (7 2 (:REWRITE AC-<))
                       (6 1 (:REWRITE O-FIRST-EXPT-<))
                       (5 1 (:DEFINITION RP::EX-FROM-RP))
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
                       (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                       (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                       (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
                       (2 1 (:REWRITE O-FIRST-COEFF-<))
                       (1 1
                          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                       (1 1
                          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::RP-MATCH-LHS-PRECHECK$INLINE)
(RP::RP-CHECK-CONTEXT)
(RP::RP-GET-DONT-RW (58 28 (:REWRITE DEFAULT-+-2))
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
                    (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                    (6 6 (:REWRITE DEFAULT-CAR))
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
                    (3 3 (:DEFINITION NOT))
                    (2 2
                       (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                    (2 2
                       (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                    (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                    (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                    (1 1 (:REWRITE O-P-DEF-O-FINP-1))
                    (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::UNQUOTE-ALL)
(RP::MAGIC-EV-FNCALL-WRAPPER)
(RP::RP-EX-COUNTERPART (250 190 (:REWRITE DEFAULT-CAR))
                       (175 175 (:REWRITE DEFAULT-CDR))
                       (135 15 (:DEFINITION ASSOC-EQUAL))
                       (132 33 (:REWRITE O-P-O-INFP-CAR))
                       (33 33 (:REWRITE O-P-DEF-O-FINP-1))
                       (30 15 (:DEFINITION NTH))
                       (26 26
                           (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                       (15 15 (:REWRITE NTH-WHEN-PREFIXP))
                       (12 12 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                       (12 1 (:DEFINITION HONS-ASSOC-EQUAL))
                       (10 10
                           (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
                       (10 1 (:DEFINITION SYMBOL-ALISTP))
                       (1 1
                          (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
                       (1 1 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
                       (1 1 (:REWRITE MEXTRACT-FNCALL))
                       (1 1 (:DEFINITION HONS-EQUAL)))
(RP::RP-EXTRACT-CONTEXT (211 19 (:DEFINITION APPLY$-BADGEP))
                        (198 94 (:REWRITE DEFAULT-+-2))
                        (165 5 (:REWRITE O<=-O-FINP-DEF))
                        (158 134 (:REWRITE DEFAULT-CDR))
                        (127 94 (:REWRITE DEFAULT-+-1))
                        (127 11
                             (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                        (120 8 (:DEFINITION LENGTH))
                        (106 7 (:DEFINITION NATP))
                        (94 12
                            (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                        (88 8 (:DEFINITION LEN))
                        (64 16 (:DEFINITION INTEGER-ABS))
                        (63 63 (:REWRITE DEFAULT-CAR))
                        (60 19 (:DEFINITION WEAK-APPLY$-BADGE-P))
                        (57 57 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                        (51 51
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                        (42 11
                            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                        (41 31 (:REWRITE DEFAULT-<-2))
                        (39 31 (:REWRITE DEFAULT-<-1))
                        (35 10
                            (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                        (34 34
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                        (24 24
                            (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                        (24 16 (:REWRITE STR::CONSP-OF-EXPLODE))
                        (22 22
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                        (20 5 (:REWRITE O-P-O-INFP-CAR))
                        (18 3 (:REWRITE O-FIRST-EXPT-<))
                        (17 17
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                        (17 5 (:REWRITE AC-<))
                        (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
                        (16 8
                            (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                        (15 15
                            (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                        (10 5 (:REWRITE O-INFP-O-FINP-O<=))
                        (8 8 (:TYPE-PRESCRIPTION LEN))
                        (8 8
                           (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                        (8 8 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                        (8 8 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                        (8 8 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                        (8 8
                           (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                        (8 8 (:REWRITE DEFAULT-REALPART))
                        (8 8 (:REWRITE DEFAULT-NUMERATOR))
                        (8 8 (:REWRITE DEFAULT-IMAGPART))
                        (8 8 (:REWRITE DEFAULT-DENOMINATOR))
                        (6 3 (:REWRITE O-FIRST-COEFF-<))
                        (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
                        (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                        (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(RP::RP-EV-FNCALL)
(RP::RP-EXC-ALL (461 212 (:REWRITE DEFAULT-+-2))
                (445 24 (:DEFINITION APPLY$-BADGEP))
                (349 295 (:REWRITE DEFAULT-CDR))
                (296 28
                     (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                (290 212 (:REWRITE DEFAULT-+-1))
                (270 18 (:DEFINITION LENGTH))
                (249 7 (:REWRITE O<=-O-FINP-DEF))
                (215 21
                     (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                (198 18 (:DEFINITION LEN))
                (186 14 (:DEFINITION NATP))
                (144 36 (:DEFINITION INTEGER-ABS))
                (115 115 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                (109 109 (:REWRITE DEFAULT-CAR))
                (83 60 (:REWRITE DEFAULT-<-2))
                (72 21
                    (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                (70 60 (:REWRITE DEFAULT-<-1))
                (68 24 (:DEFINITION WEAK-APPLY$-BADGE-P))
                (57 57
                    (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                (56 14 (:REWRITE O-P-O-INFP-CAR))
                (54 54
                    (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                (54 36 (:REWRITE STR::CONSP-OF-EXPLODE))
                (42 21
                    (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                (38 38
                    (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
                (36 18
                    (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                (32 32
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (31 7 (:REWRITE AC-<))
                (26 26
                    (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                (21 3 (:REWRITE O-FIRST-EXPT-<))
                (19 19
                    (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                (18 18 (:TYPE-PRESCRIPTION LEN))
                (18 18
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (18 18 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                (18 18 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                (18 18
                    (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                (18 18
                    (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                (18 18 (:REWRITE DEFAULT-REALPART))
                (18 18 (:REWRITE DEFAULT-NUMERATOR))
                (18 18 (:REWRITE DEFAULT-IMAGPART))
                (18 18 (:REWRITE DEFAULT-DENOMINATOR))
                (15 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (14 14 (:REWRITE O-P-DEF-O-FINP-1))
                (14 7 (:REWRITE O-INFP-O-FINP-O<=))
                (9 3 (:REWRITE O-FIRST-COEFF-<))
                (7 7 (:REWRITE |a < b & b < c  =>  a < c|))
                (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::FLAG-RP-EXC-ALL (735 348 (:REWRITE DEFAULT-+-2))
                     (495 33 (:DEFINITION LENGTH))
                     (473 348 (:REWRITE DEFAULT-+-1))
                     (450 351 (:REWRITE DEFAULT-CDR))
                     (445 24 (:DEFINITION APPLY$-BADGEP))
                     (396 14 (:REWRITE O<=-O-FINP-DEF))
                     (363 33 (:DEFINITION LEN))
                     (296 28
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                     (264 66 (:DEFINITION INTEGER-ABS))
                     (215 21
                          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                     (186 14 (:DEFINITION NATP))
                     (137 137 (:REWRITE DEFAULT-CAR))
                     (132 99 (:REWRITE DEFAULT-<-2))
                     (118 99 (:REWRITE DEFAULT-<-1))
                     (115 115 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                     (99 99
                         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                     (99 66 (:REWRITE STR::CONSP-OF-EXPLODE))
                     (81 81
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                     (72 21
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                     (68 24 (:DEFINITION WEAK-APPLY$-BADGE-P))
                     (66 66 (:REWRITE DEFAULT-UNARY-MINUS))
                     (66 33
                         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                     (64 16 (:REWRITE O-P-O-INFP-CAR))
                     (55 55
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                     (53 14 (:REWRITE AC-<))
                     (47 47
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (42 21
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                     (40 40
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                     (33 33 (:TYPE-PRESCRIPTION LEN))
                     (33 33
                         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (33 33 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                     (33 33 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                     (33 33
                         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                     (33 33
                         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                     (33 33 (:REWRITE DEFAULT-REALPART))
                     (33 33 (:REWRITE DEFAULT-NUMERATOR))
                     (33 33 (:REWRITE DEFAULT-IMAGPART))
                     (33 33 (:REWRITE DEFAULT-DENOMINATOR))
                     (33 5 (:REWRITE O-FIRST-EXPT-<))
                     (29 29
                         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                     (28 14 (:REWRITE O-INFP-O-FINP-O<=))
                     (28 2 (:TYPE-PRESCRIPTION RETURN-LAST))
                     (23 10 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                     (14 14
                         (:REWRITE |a < b & b < c  =>  a < c|))
                     (13 5 (:REWRITE O-FIRST-COEFF-<))
                     (2 2
                        (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
                     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-RP-EXC-ALL-EQUIVALENCES)
(RP::FLAG-LEMMA-FOR-PSEUDO-TERMP-RP-EXC-ALL
     (12768 82
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (10993 10993 (:REWRITE DEFAULT-CDR))
     (8019 8019 (:REWRITE DEFAULT-CAR))
     (4088 1145 (:REWRITE O-P-O-INFP-CAR))
     (3325 175 (:DEFINITION RP::UNQUOTE-ALL))
     (981 981 (:REWRITE O-P-DEF-O-FINP-1))
     (653 653 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (250 18
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (234 18 (:DEFINITION APPLY$-BADGEP))
     (169 169
          (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
     (169 169
          (:REWRITE MX-EV-META-EXTRACT-FNCALL))
     (169 169 (:REWRITE MEXTRACT-FNCALL))
     (154 154
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (96 8 (:DEFINITION NATP))
     (54 54 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (44 18 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (28 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (28 8
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (24 12
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(RP::PSEUDO-TERMP-RP-EXC-ALL)
(RP::PSEUDO-TERMP-RP-EXC-ALL-SUBTERMS)
(RP::RP-EXC-ALL (182 1 (:DEFINITION RP::RP-EXC-ALL))
                (130 5 (:DEFINITION RP::RP-EV-FNCALL))
                (122 122 (:REWRITE DEFAULT-CDR))
                (95 5 (:DEFINITION RP::UNQUOTE-ALL))
                (79 79 (:REWRITE DEFAULT-CAR))
                (36 9 (:REWRITE O-P-O-INFP-CAR))
                (15 5
                    (:DEFINITION RP::RP-APPLY-BINDINGS-SUBTERMS))
                (12 12 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                (9 9 (:REWRITE O-P-DEF-O-FINP-1))
                (5 5
                   (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
                (5 5 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
                (5 5 (:REWRITE MEXTRACT-FNCALL)))
(RP::CHECK-SYNP-SYNTAX-AUX)
(RP::RP-RW-RELIEVE-SYNP)
(RP::RP-RW-RELIEVE-SYNP-WRAP)
(RP::REMOVE-RP-FROM-BINDINGS-FOR-SYNP
     (671 3 (:DEFINITION RP::RP-TERMP))
     (597 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (462 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (337 337 (:REWRITE DEFAULT-CDR))
     (243 243 (:REWRITE DEFAULT-CAR))
     (138 39 (:REWRITE O-P-O-INFP-CAR))
     (58 9 (:DEFINITION RP::INCLUDE-FNC))
     (33 33 (:REWRITE O-P-DEF-O-FINP-1))
     (23 9 (:DEFINITION QUOTEP))
     (20 20 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (12 3
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (7 1 (:DEFINITION ALISTP))
     (5 5
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (3 3 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (3 3
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-RW-RULE-AUX)
(RP::RP-RW-META-RULE)
(RP::RP-FORMULA-CHECKS)
(RP::RP-RW-META-RULE-VALID-EVAL)
(RP::RP-RW-META-RULE-VALID-RP-TERMP
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (202 202 (:REWRITE DEFAULT-CDR))
     (138 138 (:REWRITE DEFAULT-CAR))
     (76 22 (:REWRITE O-P-O-INFP-CAR))
     (36 36 (:TYPE-PRESCRIPTION O-P))
     (18 18 (:REWRITE O-P-DEF-O-FINP-1))
     (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::RP-RW-META-RULE-VALID-DONT-RW-SYNTAXP)
(RP::RP-RW-META-RULES)
(RP::CHECK-IF-RELIEVED-WITH-RP-AUX
     (63 32 (:REWRITE DEFAULT-+-2))
     (54 48 (:REWRITE DEFAULT-CDR))
     (41 32 (:REWRITE DEFAULT-+-1))
     (37 37 (:REWRITE DEFAULT-CAR))
     (30 2 (:DEFINITION LENGTH))
     (22 2 (:DEFINITION LEN))
     (16 4 (:DEFINITION INTEGER-ABS))
     (13 1 (:REWRITE O<=-O-FINP-DEF))
     (12 4 (:DEFINITION APPLY$-BADGEP))
     (12 3 (:REWRITE O-P-O-INFP-CAR))
     (10 2
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (10 2
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (8 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (6 6
        (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (6 5 (:REWRITE DEFAULT-<-2))
     (6 5 (:REWRITE DEFAULT-<-1))
     (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
     (4 4 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 2
        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (3 3 (:REWRITE O-P-DEF-O-FINP-1))
     (3 1 (:REWRITE AC-<))
     (2 2 (:TYPE-PRESCRIPTION LEN))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (2 2 (:REWRITE DEFAULT-REALPART))
     (2 2 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-IMAGPART))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 1 (:REWRITE O-INFP-O-FINP-O<=))
     (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
     (1 1
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::CHECK-IF-RELIEVED-WITH-RP)
(RP::RP-RW-FIX-HARD-ERROR-ALIST
     (182 84 (:REWRITE DEFAULT-+-2))
     (111 84 (:REWRITE DEFAULT-+-1))
     (102 90 (:REWRITE DEFAULT-CDR))
     (60 60 (:REWRITE DEFAULT-CAR))
     (60 4 (:DEFINITION LENGTH))
     (59 2 (:REWRITE O<=-O-FINP-DEF))
     (44 4 (:DEFINITION LEN))
     (32 8 (:DEFINITION INTEGER-ABS))
     (28 7 (:REWRITE O-P-O-INFP-CAR))
     (24 8 (:DEFINITION APPLY$-BADGEP))
     (20 4
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (20 4
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (16 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (15 10 (:REWRITE DEFAULT-<-2))
     (12 12
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (12 10 (:REWRITE DEFAULT-<-1))
     (12 8 (:REWRITE STR::CONSP-OF-EXPLODE))
     (9 2 (:REWRITE AC-<))
     (8 8 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 4
        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (7 7 (:REWRITE O-P-DEF-O-FINP-1))
     (6 6
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
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
     (4 4
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (4 4
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (4 2 (:REWRITE O-INFP-O-FINP-O<=))
     (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1)))
(RP::RP-RW-FIX-CW-LIST (144 69 (:REWRITE DEFAULT-+-2))
                       (138 4 (:REWRITE O<=-O-FINP-DEF))
                       (93 69 (:REWRITE DEFAULT-+-1))
                       (90 6 (:DEFINITION LENGTH))
                       (69 51 (:REWRITE DEFAULT-CDR))
                       (66 6 (:DEFINITION LEN))
                       (48 48
                           (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                       (48 12 (:DEFINITION INTEGER-ABS))
                       (32 32
                           (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                       (27 19 (:REWRITE DEFAULT-<-2))
                       (26 19 (:REWRITE DEFAULT-<-1))
                       (24 24 (:REWRITE DEFAULT-CAR))
                       (24 6 (:DEFINITION APPLY$-BADGEP))
                       (21 3
                           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                       (20 20
                           (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                       (18 18
                           (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                       (18 12 (:REWRITE STR::CONSP-OF-EXPLODE))
                       (18 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
                       (18 3 (:REWRITE O-FIRST-EXPT-<))
                       (16 16
                           (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                       (15 3
                           (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                       (13 4 (:REWRITE AC-<))
                       (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
                       (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                       (12 6
                           (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                       (12 3 (:REWRITE O-P-O-INFP-CAR))
                       (8 4 (:REWRITE O-INFP-O-FINP-O<=))
                       (6 6 (:TYPE-PRESCRIPTION LEN))
                       (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                       (6 6
                          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                       (6 6 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                       (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                       (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                       (6 6
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (6 6
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                       (6 6 (:REWRITE DEFAULT-REALPART))
                       (6 6 (:REWRITE DEFAULT-NUMERATOR))
                       (6 6 (:REWRITE DEFAULT-IMAGPART))
                       (6 6 (:REWRITE DEFAULT-DENOMINATOR))
                       (6 3 (:REWRITE O-FIRST-COEFF-<))
                       (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
                       (3 3 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::TRUE-LISTP-RP-RW-FIX-CW-LIST)
(RP::RP-RW-CHECK-HARD-ERROR-OR-CW)
(RP::RP-RW-RULE (12173 94 (:DEFINITION RP::RP-CHECK-CONTEXT))
                (6533 282 (:DEFINITION RP::RP-EQUAL-CNT))
                (4923 4541 (:REWRITE DEFAULT-CDR))
                (3995 752 (:DEFINITION RP::EX-FROM-RP))
                (3729 3715 (:REWRITE DEFAULT-CAR))
                (2726 94 (:DEFINITION RP::RP-EQUAL))
                (1081 1081
                      (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                (792 198 (:REWRITE O-P-O-INFP-CAR))
                (674 674 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                (235 235
                     (:TYPE-PRESCRIPTION RP::RP-EQUAL-CNT))
                (133 1 (:DEFINITION RP::RP-RW-RULE-AUX))
                (94 94 (:TYPE-PRESCRIPTION RP::RP-EQUAL))
                (88 2 (:DEFINITION RP::RP-MATCH-LHS))
                (44 44 (:REWRITE DEFAULT-<-2))
                (44 44 (:REWRITE DEFAULT-<-1))
                (42 14 (:REWRITE O<=-O-FINP-DEF))
                (38 2
                    (:DEFINITION RP::SHOULD-TERM-BE-IN-CONS$INLINE))
                (26 26 (:REWRITE DEFAULT-+-2))
                (26 26 (:REWRITE DEFAULT-+-1))
                (24 12
                    (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                (20 2
                    (:DEFINITION RP::IS-QUOTED-PAIR$INLINE))
                (16 2 (:DEFINITION RP::IS-CONS$INLINE))
                (14 14
                    (:REWRITE |a < b & b < c  =>  a < c|))
                (14 14 (:REWRITE O-INFP-O-FINP-O<=))
                (14 14 (:REWRITE AC-<))
                (14 2
                    (:DEFINITION RP::PUT-TERM-IN-CONS$INLINE))
                (14 1 (:DEFINITION RP::RP-IFF-FLAG$INLINE))
                (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
                (12 2 (:DEFINITION RP::RP-LHS$INLINE))
                (10 2 (:DEFINITION RP::RP-RULE-FNC$INLINE))
                (7 7 (:REWRITE ZP-OPEN))
                (6 6 (:TYPE-PRESCRIPTION O-FINP))
                (2 2
                   (:TYPE-PRESCRIPTION RP::RP-MATCH-LHS-PRECHECK$INLINE))
                (2 2
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (2 2 (:REWRITE CDR-CONS))
                (2 2 (:DEFINITION ASSOC-EQUAL))
                (2 2 (:DEFINITION ACONS)))
(RP::ATTACH-SC (270 270 (:REWRITE RP::MEASURE-LEMMA1))
               (234 94 (:REWRITE RP::MEASURE-LEMMA1-2))
               (168 112 (:REWRITE DEFAULT-CDR))
               (39 4 (:REWRITE O<=-O-FINP-DEF))
               (16 4 (:REWRITE O-P-O-INFP-CAR))
               (14 14 (:REWRITE DEFAULT-CAR))
               (12 6 (:REWRITE DEFAULT-<-2))
               (12 3 (:REWRITE O-FIRST-EXPT-<))
               (8 4 (:REWRITE AC-<))
               (6 6
                  (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
               (6 6
                  (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
               (6 6 (:REWRITE DEFAULT-<-1))
               (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
               (6 3 (:REWRITE O-FIRST-COEFF-<))
               (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
               (4 4 (:REWRITE O-P-DEF-O-FINP-1))
               (4 4 (:REWRITE O-INFP-O-FINP-O<=))
               (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
               (3 3
                  (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
               (3 2 (:REWRITE DEFAULT-+-2))
               (3 2 (:REWRITE DEFAULT-+-1)))
(RP::ATTACH-SC-FROM-CONTEXT)
(RP::RP-RW-AUX)
