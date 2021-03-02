(ADE::LATCH-N-BODY)
(ADE::LATCH-N* (8 4 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
               (4 4 (:TYPE-PRESCRIPTION POSP)))
(ADE::LATCH-N*$DESTRUCTURE (90 45 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
                           (45 45 (:TYPE-PRESCRIPTION POSP))
                           (24 6 (:DEFINITION ADE::LATCH-N-BODY))
                           (10 10 (:REWRITE DEFAULT-CDR))
                           (6 6 (:REWRITE ZP-OPEN))
                           (6 6 (:REWRITE DEFAULT-+-2))
                           (6 6 (:REWRITE DEFAULT-+-1))
                           (5 5 (:REWRITE DEFAULT-CAR)))
(ADE::NOT-PRIMP-LATCH-N)
(ADE::LATCH-N&)
(ADE::LATCH-N$NETLIST)
(ADE::CHECK-LATCH-N$NETLIST-64)
(ADE::LATCH-N-BODY-INDUCT)
(ADE::LATCH-N$UNBOUND-IN-BODY (51 51
                                  (:TYPE-PRESCRIPTION ADE::LATCH-N-BODY))
                              (27 27 (:REWRITE DEFAULT-CDR))
                              (27 27 (:REWRITE DEFAULT-CAR))
                              (27 27 (:REWRITE DEFAULT-<-2))
                              (27 27 (:REWRITE DEFAULT-<-1))
                              (22 18 (:REWRITE DEFAULT-+-2))
                              (18 18 (:REWRITE DEFAULT-+-1))
                              (15 9 (:REWRITE ZP-OPEN))
                              (12 6 (:REWRITE DEFAULT-SYMBOL-NAME))
                              (12 4 (:REWRITE FOLD-CONSTS-IN-+))
                              (4 4
                                 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ADE::LATCH-N$ALL-UNBOUND-IN-BODY
     (51 6
         (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
     (30 15 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
     (15 15 (:TYPE-PRESCRIPTION ADE::SIS))
     (15 15 (:TYPE-PRESCRIPTION POSP))
     (12 12
         (:TYPE-PRESCRIPTION ADE::LATCH-N-BODY))
     (6 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(ADE::LATCH-N-BODY$VALUE
     (702 436 (:REWRITE DEFAULT-CDR))
     (677 435 (:REWRITE DEFAULT-CAR))
     (602 560 (:REWRITE DEFAULT-+-2))
     (560 560 (:REWRITE DEFAULT-+-1))
     (534 267 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
     (453 113 (:REWRITE ZP-OPEN))
     (320 22
          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
     (267 267 (:TYPE-PRESCRIPTION ADE::SIS))
     (267 267 (:TYPE-PRESCRIPTION POSP))
     (180 90
          (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
     (175 31
          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
     (169 13 (:DEFINITION MEMBER-EQUAL))
     (153 9
          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
     (127 127 (:REWRITE DEFAULT-<-2))
     (127 127 (:REWRITE DEFAULT-<-1))
     (120 40 (:REWRITE ADE::V-THREEFIX-BVP))
     (94 44 (:REWRITE ADE::F-GATES=B-GATES))
     (80 80 (:TYPE-PRESCRIPTION ADE::BVP))
     (78 78 (:TYPE-PRESCRIPTION ADE::SE))
     (78 13 (:DEFINITION BINARY-APPEND))
     (68 12 (:REWRITE REPEAT-WHEN-ZP))
     (65 65 (:TYPE-PRESCRIPTION PAIRLIS$))
     (61 22
         (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
     (52 52 (:LINEAR LEN-WHEN-PREFIXP))
     (44 44
         (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
     (26 26
         (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (13 13 (:REWRITE DEFAULT-SYMBOL-NAME))
     (12 12 (:TYPE-PRESCRIPTION ADE::3VP)))
(ADE::LATCH-N$VALUE (72 1 (:DEFINITION ADE::SE-OCC))
                    (57 29 (:REWRITE DEFAULT-+-2))
                    (30 10 (:REWRITE ADE::BV-IS-TRUE-LIST))
                    (29 29 (:REWRITE DEFAULT-+-1))
                    (29 1
                        (:REWRITE ADE::ASSOC-EQ-VALUE-PAIRLIS$-NOT-MEMBER))
                    (28 3
                        (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
                    (27 2 (:DEFINITION MEMBER-EQUAL))
                    (27 1
                        (:REWRITE ADE::ASSOC-EQ-VALUES-ARGS-PAIRLIS$-ARGS))
                    (20 20 (:TYPE-PRESCRIPTION ADE::BVP))
                    (20 1 (:REWRITE LEN-WHEN-PREFIXP))
                    (18 18 (:LINEAR LEN-WHEN-PREFIXP))
                    (17 3 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
                    (14 1 (:DEFINITION ADE::LATCH-N-BODY))
                    (12 3
                        (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                                  . 2))
                    (11 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
                    (9 9
                       (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
                    (8 4 (:REWRITE ADE::FV-IF-WHEN-BVP))
                    (8 1 (:REWRITE ZP-OPEN))
                    (6 2 (:REWRITE ADE::LEN-SIS))
                    (5 5 (:TYPE-PRESCRIPTION PREFIXP))
                    (5 5 (:TYPE-PRESCRIPTION PAIRLIS$))
                    (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                    (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                    (4 4 (:REWRITE DEFAULT-SYMBOL-NAME))
                    (4 4 (:DEFINITION STRIP-CARS))
                    (4 2 (:REWRITE ADE::NFIX-OF-NAT))
                    (4 2 (:REWRITE DEFAULT-<-2))
                    (4 1 (:DEFINITION BINARY-APPEND))
                    (3 3
                       (:TYPE-PRESCRIPTION ADE::LATCH-N-BODY))
                    (3 2 (:REWRITE DEFAULT-<-1))
                    (2 2 (:REWRITE TAKE-WHEN-ATOM))
                    (2 2
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                    (2 2
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                    (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                    (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                    (2 2
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                    (2 2
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                    (2 2
                       (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
                    (2 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
                    (1 1
                       (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
                    (1 1 (:REWRITE ADE::NO-DUPLICATESP-SIS))
                    (1 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
                    (1 1 (:DEFINITION ADE::OCC-NAME$INLINE))
                    (1 1 (:DEFINITION ADE::OCC-INS$INLINE))
                    (1 1 (:DEFINITION ADE::OCC-FN$INLINE)))
(ADE::LATCH-N-BODY-STATE-INDUCT
     (6 6
        (:TYPE-PRESCRIPTION ADE::DE-OCC-BINDINGS)))
(ADE::LATCH-N-BODY$STATE-AUX-1 (43 40 (:REWRITE DEFAULT-CAR))
                               (12 10 (:REWRITE DEFAULT-CDR)))
(ADE::LATCH-N-BODY$STATE-AUX-2
     (16 14 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 3
         (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                   . 2))
     (11 9 (:REWRITE DEFAULT-CDR))
     (6 6
        (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE DEFAULT-SYMBOL-NAME)))
(ADE::LATCH-N-BODY$STATE
     (648 419 (:REWRITE DEFAULT-CAR))
     (554 368 (:REWRITE DEFAULT-CDR))
     (516 486 (:REWRITE DEFAULT-+-2))
     (500 120 (:REWRITE ZP-OPEN))
     (486 486 (:REWRITE DEFAULT-+-1))
     (372 15
          (:REWRITE ADE::ASSOC-EQ-VALUES-DE-OCC-UPDATE-ALIST))
     (342 39 (:DEFINITION MEMBER-EQUAL))
     (236 26
          (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
     (162 24 (:DEFINITION ALISTP))
     (157 157 (:REWRITE DEFAULT-<-2))
     (157 157 (:REWRITE DEFAULT-<-1))
     (146 68
          (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
     (138 26 (:REWRITE REPEAT-WHEN-ZP))
     (129 39
          (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                    . 2))
     (120 120 (:TYPE-PRESCRIPTION ALISTP))
     (117 15 (:DEFINITION ASSOC-EQUAL))
     (84 28 (:REWRITE ADE::V-THREEFIX-BVP))
     (66 24 (:REWRITE CONSP-OF-REPEAT))
     (63 9
         (:REWRITE ADE::ASSOC-EQ-VALUE-UPDATE-ALIST-2))
     (56 56 (:TYPE-PRESCRIPTION ADE::BVP))
     (40 4 (:REWRITE ADE::CAR-V-THREEFIX))
     (36 36
         (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (36 9
         (:REWRITE ADE::UPDATE-ALIST-DIFF-KEYS))
     (34 33 (:REWRITE DEFAULT-SYMBOL-NAME))
     (33 33 (:REWRITE ADE::SUBSETP-TRANSITIVITY))
     (31 13 (:REWRITE ADE::F-GATES=B-GATES))
     (28 10 (:REWRITE ADE::SI-MEMBER-SIS))
     (27 9
         (:REWRITE ADE::ASSOC-EQ-VALUE-UPDATE-ALIST-1))
     (18 18
         (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (12 4 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
     (6 6
        (:REWRITE ADE::ASSOC-EQ-VALUE-DE-OCC-UPDATE-ALIST-DIFF-NAMES)))
(ADE::LATCH-N$STATE (76 1 (:DEFINITION ADE::DE-OCC))
                    (72 1 (:DEFINITION ADE::SE-OCC))
                    (63 32 (:REWRITE DEFAULT-+-2))
                    (58 2
                        (:REWRITE ADE::ASSOC-EQ-VALUE-PAIRLIS$-NOT-MEMBER))
                    (49 3 (:DEFINITION MEMBER-EQUAL))
                    (45 4
                        (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
                    (32 32 (:REWRITE DEFAULT-+-1))
                    (30 10 (:REWRITE ADE::BV-IS-TRUE-LIST))
                    (27 1
                        (:REWRITE ADE::ASSOC-EQ-VALUES-ARGS-PAIRLIS$-ARGS))
                    (22 22 (:LINEAR LEN-WHEN-PREFIXP))
                    (20 20 (:TYPE-PRESCRIPTION ADE::BVP))
                    (20 1 (:REWRITE LEN-WHEN-PREFIXP))
                    (18 4 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
                    (15 1
                        (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
                    (14 1 (:DEFINITION ADE::LATCH-N-BODY))
                    (12 3
                        (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                                  . 2))
                    (11 11
                        (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
                    (11 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
                    (8 8 (:TYPE-PRESCRIPTION ADE::FV-IF))
                    (8 4 (:REWRITE ADE::FV-IF-WHEN-BVP))
                    (8 1 (:REWRITE ZP-OPEN))
                    (6 2 (:REWRITE ADE::LEN-SIS))
                    (5 5 (:TYPE-PRESCRIPTION PREFIXP))
                    (5 5
                       (:TYPE-PRESCRIPTION ADE::LATCH-N-BODY))
                    (5 5 (:REWRITE DEFAULT-SYMBOL-NAME))
                    (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                    (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                    (4 4 (:DEFINITION STRIP-CARS))
                    (4 2 (:REWRITE ADE::NFIX-OF-NAT))
                    (4 2 (:REWRITE DEFAULT-<-2))
                    (4 1 (:DEFINITION BINARY-APPEND))
                    (3 2 (:REWRITE DEFAULT-<-1))
                    (2 2 (:REWRITE TAKE-WHEN-ATOM))
                    (2 2
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                    (2 2
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                    (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                    (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                    (2 2
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                    (2 2
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                    (2 2
                       (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
                    (2 2 (:DEFINITION ADE::OCC-NAME$INLINE))
                    (2 2 (:DEFINITION ADE::OCC-INS$INLINE))
                    (2 2 (:DEFINITION ADE::OCC-FN$INLINE))
                    (2 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
                    (1 1
                       (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
                    (1 1 (:REWRITE ADE::NO-DUPLICATESP-SIS))
                    (1 1
                       (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
                    (1 1
                       (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
                    (1 1 (:REWRITE ADE::ALISTP-PAIRLIS$))
                    (1 1 (:DEFINITION ADE::OCC-OUTS$INLINE)))
(ADE::FF-N-BODY)
(ADE::FF-N* (8 4 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
            (4 4 (:TYPE-PRESCRIPTION POSP)))
(ADE::FF-N*$DESTRUCTURE (90 45 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
                        (45 45 (:TYPE-PRESCRIPTION POSP))
                        (24 6 (:DEFINITION ADE::FF-N-BODY))
                        (10 10 (:REWRITE DEFAULT-CDR))
                        (6 6 (:REWRITE ZP-OPEN))
                        (6 6 (:REWRITE DEFAULT-+-2))
                        (6 6 (:REWRITE DEFAULT-+-1))
                        (5 5 (:REWRITE DEFAULT-CAR)))
(ADE::NOT-PRIMP-FF-N)
(ADE::FF-N&)
(ADE::FF-N$NETLIST)
(ADE::CHECK-FF-N$NETLIST-64)
(ADE::FF-N-BODY-INDUCT)
(ADE::FF-N$UNBOUND-IN-BODY (51 51 (:TYPE-PRESCRIPTION ADE::FF-N-BODY))
                           (27 27 (:REWRITE DEFAULT-CDR))
                           (27 27 (:REWRITE DEFAULT-CAR))
                           (27 27 (:REWRITE DEFAULT-<-2))
                           (27 27 (:REWRITE DEFAULT-<-1))
                           (22 18 (:REWRITE DEFAULT-+-2))
                           (18 18 (:REWRITE DEFAULT-+-1))
                           (15 9 (:REWRITE ZP-OPEN))
                           (12 6 (:REWRITE DEFAULT-SYMBOL-NAME))
                           (12 4 (:REWRITE FOLD-CONSTS-IN-+))
                           (4 4
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ADE::FF-N$ALL-UNBOUND-IN-BODY
     (51 6
         (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
     (30 15 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
     (15 15 (:TYPE-PRESCRIPTION ADE::SIS))
     (15 15 (:TYPE-PRESCRIPTION POSP))
     (12 12 (:TYPE-PRESCRIPTION ADE::FF-N-BODY))
     (6 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(ADE::FF-N-BODY$VALUE (129 86 (:REWRITE DEFAULT-CAR))
                      (112 78 (:REWRITE DEFAULT-CDR))
                      (88 28 (:REWRITE FOLD-CONSTS-IN-+))
                      (80 40 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
                      (73 68 (:REWRITE DEFAULT-+-2))
                      (68 68 (:REWRITE DEFAULT-+-1))
                      (62 4
                          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
                      (56 3
                          (:REWRITE ADE::ASSOC-EQ-VALUES-CONS-NOT-MEMBER))
                      (55 16 (:REWRITE ZP-OPEN))
                      (40 40 (:TYPE-PRESCRIPTION ADE::SIS))
                      (40 40 (:TYPE-PRESCRIPTION POSP))
                      (39 3 (:DEFINITION MEMBER-EQUAL))
                      (35 5
                          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
                      (32 32 (:TYPE-PRESCRIPTION ADE::F-BUF))
                      (24 12
                          (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
                      (24 8 (:REWRITE ADE::V-THREEFIX-BVP))
                      (23 13 (:REWRITE ADE::F-GATES=B-GATES))
                      (20 20 (:TYPE-PRESCRIPTION BOOLEANP))
                      (18 18 (:TYPE-PRESCRIPTION ADE::SE))
                      (18 3 (:DEFINITION BINARY-APPEND))
                      (17 7 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
                      (17 1
                          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
                      (16 16 (:TYPE-PRESCRIPTION ADE::BVP))
                      (16 16 (:REWRITE DEFAULT-<-2))
                      (16 16 (:REWRITE DEFAULT-<-1))
                      (16 8 (:REWRITE ADE::LEN-SIS))
                      (15 15 (:TYPE-PRESCRIPTION PAIRLIS$))
                      (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                      (13 4
                          (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
                      (12 12 (:LINEAR LEN-WHEN-PREFIXP))
                      (12 3
                          (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                                    . 2))
                      (8 8
                         (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
                      (8 8 (:REWRITE ADE::NFIX-OF-NAT))
                      (6 6
                         (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
                      (6 6
                         (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
                      (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
                      (4 2 (:REWRITE UNICITY-OF-0))
                      (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
                      (2 2 (:DEFINITION FIX)))
(ADE::FF-N$VALUE (72 1 (:DEFINITION ADE::SE-OCC))
                 (29 1
                     (:REWRITE ADE::ASSOC-EQ-VALUE-PAIRLIS$-NOT-MEMBER))
                 (27 2 (:DEFINITION MEMBER-EQUAL))
                 (20 5 (:DEFINITION LEN))
                 (17 1
                     (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
                 (15 8 (:REWRITE DEFAULT-+-2))
                 (14 1 (:DEFINITION ADE::FF-N-BODY))
                 (9 1
                    (:REWRITE ADE::ASSOC-EQ-VALUES-CONS-NOT-MEMBER))
                 (8 8 (:REWRITE DEFAULT-+-1))
                 (8 2
                    (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                              . 2))
                 (8 1 (:REWRITE ZP-OPEN))
                 (6 6
                    (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
                 (6 6 (:TYPE-PRESCRIPTION ADE::BVP))
                 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
                 (5 5 (:TYPE-PRESCRIPTION PAIRLIS$))
                 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                 (4 2 (:REWRITE ADE::V-THREEFIX-BVP))
                 (4 1
                    (:REWRITE ADE::NOT-MEMBER-WITH-SIS-OF-DIFF-SYMBOL))
                 (4 1 (:DEFINITION TRUE-LISTP))
                 (4 1 (:DEFINITION BINARY-APPEND))
                 (3 3 (:TYPE-PRESCRIPTION ADE::FF-N-BODY))
                 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
                 (2 2
                    (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
                 (2 2 (:DEFINITION STRIP-CARS))
                 (2 1 (:REWRITE DEFAULT-<-2))
                 (1 1 (:REWRITE TAKE-WHEN-ATOM))
                 (1 1
                    (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
                 (1 1 (:REWRITE DEFAULT-<-1))
                 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
                 (1 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
                 (1 1 (:DEFINITION ADE::OCC-NAME$INLINE))
                 (1 1 (:DEFINITION ADE::OCC-INS$INLINE))
                 (1 1 (:DEFINITION ADE::OCC-FN$INLINE)))
(ADE::FF-N-BODY-STATE-INDUCT (6 6
                                (:TYPE-PRESCRIPTION ADE::DE-OCC-BINDINGS)))
(ADE::FF-N-BODY$STATE-AUX-1)
(ADE::FF-N-BODY$STATE-AUX-2
     (16 14 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 3
         (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                   . 2))
     (11 9 (:REWRITE DEFAULT-CDR))
     (6 6
        (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE DEFAULT-SYMBOL-NAME)))
(ADE::FF-N-BODY$STATE
     (648 419 (:REWRITE DEFAULT-CAR))
     (554 368 (:REWRITE DEFAULT-CDR))
     (516 486 (:REWRITE DEFAULT-+-2))
     (500 120 (:REWRITE ZP-OPEN))
     (486 486 (:REWRITE DEFAULT-+-1))
     (372 15
          (:REWRITE ADE::ASSOC-EQ-VALUES-DE-OCC-UPDATE-ALIST))
     (342 39 (:DEFINITION MEMBER-EQUAL))
     (236 26
          (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
     (162 24 (:DEFINITION ALISTP))
     (157 157 (:REWRITE DEFAULT-<-2))
     (157 157 (:REWRITE DEFAULT-<-1))
     (146 68
          (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
     (138 26 (:REWRITE REPEAT-WHEN-ZP))
     (129 39
          (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                    . 2))
     (120 120 (:TYPE-PRESCRIPTION ALISTP))
     (117 15 (:DEFINITION ASSOC-EQUAL))
     (84 28 (:REWRITE ADE::V-THREEFIX-BVP))
     (66 24 (:REWRITE CONSP-OF-REPEAT))
     (63 9
         (:REWRITE ADE::ASSOC-EQ-VALUE-UPDATE-ALIST-2))
     (56 56 (:TYPE-PRESCRIPTION ADE::BVP))
     (40 4 (:REWRITE ADE::CAR-V-THREEFIX))
     (36 36
         (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (36 9
         (:REWRITE ADE::UPDATE-ALIST-DIFF-KEYS))
     (34 33 (:REWRITE DEFAULT-SYMBOL-NAME))
     (33 33 (:REWRITE ADE::SUBSETP-TRANSITIVITY))
     (31 13 (:REWRITE ADE::F-GATES=B-GATES))
     (28 10 (:REWRITE ADE::SI-MEMBER-SIS))
     (27 9
         (:REWRITE ADE::ASSOC-EQ-VALUE-UPDATE-ALIST-1))
     (18 18
         (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (12 4 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
     (6 6
        (:REWRITE ADE::ASSOC-EQ-VALUE-DE-OCC-UPDATE-ALIST-DIFF-NAMES)))
(ADE::FF-N$STATE (82 1 (:DEFINITION ADE::DE-OCC))
                 (72 1 (:DEFINITION ADE::SE-OCC))
                 (63 32 (:REWRITE DEFAULT-+-2))
                 (62 31
                     (:TYPE-PRESCRIPTION ADE::LATCH-N-BODY$STATE-AUX-1))
                 (58 2
                     (:REWRITE ADE::ASSOC-EQ-VALUE-PAIRLIS$-NOT-MEMBER))
                 (49 3 (:DEFINITION MEMBER-EQUAL))
                 (45 4
                     (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
                 (32 32 (:REWRITE DEFAULT-+-1))
                 (30 10 (:REWRITE ADE::BV-IS-TRUE-LIST))
                 (27 1
                     (:REWRITE ADE::ASSOC-EQ-VALUES-ARGS-PAIRLIS$-ARGS))
                 (22 22 (:LINEAR LEN-WHEN-PREFIXP))
                 (21 1
                     (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
                 (20 20 (:TYPE-PRESCRIPTION ADE::BVP))
                 (20 1 (:REWRITE LEN-WHEN-PREFIXP))
                 (18 4 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
                 (14 1 (:DEFINITION ADE::FF-N-BODY))
                 (12 3
                     (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL
                               . 2))
                 (11 11
                     (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
                 (11 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
                 (8 8 (:TYPE-PRESCRIPTION ADE::FV-IF))
                 (8 4 (:REWRITE ADE::FV-IF-WHEN-BVP))
                 (8 1 (:REWRITE ZP-OPEN))
                 (6 2 (:REWRITE ADE::LEN-SIS))
                 (5 5 (:TYPE-PRESCRIPTION PREFIXP))
                 (5 5 (:TYPE-PRESCRIPTION ADE::FF-N-BODY))
                 (5 5 (:REWRITE DEFAULT-SYMBOL-NAME))
                 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                 (4 4 (:DEFINITION STRIP-CARS))
                 (4 2 (:REWRITE ADE::NFIX-OF-NAT))
                 (4 2 (:REWRITE DEFAULT-<-2))
                 (4 1 (:DEFINITION BINARY-APPEND))
                 (3 2 (:REWRITE DEFAULT-<-1))
                 (2 2 (:REWRITE TAKE-WHEN-ATOM))
                 (2 2
                    (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                 (2 2
                    (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                 (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                 (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                 (2 2
                    (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                 (2 2
                    (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                 (2 2
                    (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
                 (2 2 (:DEFINITION ADE::OCC-NAME$INLINE))
                 (2 2 (:DEFINITION ADE::OCC-INS$INLINE))
                 (2 2 (:DEFINITION ADE::OCC-FN$INLINE))
                 (2 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
                 (1 1
                    (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
                 (1 1 (:REWRITE ADE::NO-DUPLICATESP-SIS))
                 (1 1
                    (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
                 (1 1
                    (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
                 (1 1 (:REWRITE ADE::ALISTP-PAIRLIS$))
                 (1 1 (:DEFINITION ADE::OCC-OUTS$INLINE)))
