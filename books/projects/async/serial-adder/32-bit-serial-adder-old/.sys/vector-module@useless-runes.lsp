(ADE::VECTOR-MODULE-INDUCTION)
(ADE::V-BUF-BODY)
(ADE::V-BUF*
 (4 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-BUF*$DESTRUCTURE
 (60 30 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (30 30 (:TYPE-PRESCRIPTION POSP))
 (24 6 (:DEFINITION ADE::V-BUF-BODY))
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-V-BUF)
(ADE::V-BUF&)
(ADE::V-BUF$NETLIST)
(ADE::V-BUF$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-BUF-BODY$VALUE
 (115 112 (:REWRITE DEFAULT-+-2))
 (112 112 (:REWRITE DEFAULT-+-1))
 (110 77 (:REWRITE DEFAULT-CDR))
 (100 32 (:REWRITE FOLD-CONSTS-IN-+))
 (95 66 (:REWRITE DEFAULT-CAR))
 (76 38 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (63 18 (:REWRITE ZP-OPEN))
 (62 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (39 3 (:DEFINITION MEMBER-EQUAL))
 (38 38 (:TYPE-PRESCRIPTION ADE::SIS))
 (38 38 (:TYPE-PRESCRIPTION POSP))
 (35 5 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (33 33 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (24 8 (:REWRITE ADE::V-THREEFIX-BVP))
 (20 20 (:TYPE-PRESCRIPTION BOOLEANP))
 (18 18 (:TYPE-PRESCRIPTION ADE::SE))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (18 9 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (18 3 (:DEFINITION BINARY-APPEND))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (16 16 (:TYPE-PRESCRIPTION ADE::BVP))
 (16 8 (:REWRITE ADE::LEN-SIS))
 (16 6 (:REWRITE ADE::F-GATES=B-GATES))
 (16 6 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (15 15 (:TYPE-PRESCRIPTION PAIRLIS$))
 (13 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (8 8 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (8 8 (:REWRITE ADE::NFIX-OF-NAT))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (6 6 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 2 (:REWRITE UNICITY-OF-0))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:DEFINITION FIX))
 )
(ADE::V-BUF$VALUE
 (59 1 (:DEFINITION ADE::SE-OCC))
 (51 35 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION LEN))
 (23 20 (:REWRITE DEFAULT-CAR))
 (19 10 (:REWRITE DEFAULT-+-2))
 (18 1 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (16 2 (:DEFINITION ADE::V-THREEFIX))
 (14 1 (:DEFINITION ADE::V-BUF-BODY))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (11 10 (:REWRITE DEFAULT-+-1))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (10 10 (:TYPE-PRESCRIPTION ADE::BVP))
 (10 4 (:REWRITE ADE::V-THREEFIX-BVP))
 (8 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 5 (:TYPE-PRESCRIPTION PAIRLIS$))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 2 (:DEFINITION ADE::3V-FIX))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (2 2 (:TYPE-PRESCRIPTION ADE::SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:TYPE-PRESCRIPTION ADE::3VP))
 (2 2 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-NOT-BODY)
(ADE::V-NOT*
 (4 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-NOT*$DESTRUCTURE
 (60 30 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (30 30 (:TYPE-PRESCRIPTION POSP))
 (24 6 (:DEFINITION ADE::V-NOT-BODY))
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-V-NOT)
(ADE::V-NOT&)
(ADE::V-NOT$NETLIST)
(ADE::V-NOT$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-NOT-BODY$VALUE
 (103 101 (:REWRITE DEFAULT-+-2))
 (101 101 (:REWRITE DEFAULT-+-1))
 (94 30 (:REWRITE FOLD-CONSTS-IN-+))
 (87 62 (:REWRITE DEFAULT-CDR))
 (74 53 (:REWRITE DEFAULT-CAR))
 (58 16 (:REWRITE ZP-OPEN))
 (54 27 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (28 8 (:REWRITE ADE::F-GATES=B-GATES))
 (27 27 (:TYPE-PRESCRIPTION ADE::SIS))
 (27 27 (:TYPE-PRESCRIPTION POSP))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (18 6 (:REWRITE ADE::FV-NOT=V-NOT))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 12 (:TYPE-PRESCRIPTION ADE::BVP))
 (12 6 (:REWRITE ADE::LEN-SIS))
 (12 6 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 6 (:REWRITE ADE::NFIX-OF-NAT))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE UNICITY-OF-0))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:DEFINITION FIX))
 )
(ADE::V-NOT$VALUE
 (59 1 (:DEFINITION ADE::SE-OCC))
 (49 33 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION LEN))
 (21 18 (:REWRITE DEFAULT-CAR))
 (19 10 (:REWRITE DEFAULT-+-2))
 (18 1 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (14 1 (:DEFINITION ADE::V-NOT-BODY))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (11 10 (:REWRITE DEFAULT-+-1))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (8 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (6 6 (:TYPE-PRESCRIPTION ADE::BVP))
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 5 (:TYPE-PRESCRIPTION PAIRLIS$))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 2 (:REWRITE ADE::FV-NOT=V-NOT))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (2 2 (:TYPE-PRESCRIPTION ADE::SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-AND-BODY)
(ADE::V-AND*
 (12 6 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-AND*$DESTRUCTURE
 (150 75 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (75 75 (:TYPE-PRESCRIPTION POSP))
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (24 6 (:DEFINITION ADE::V-AND-BODY))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(ADE::NOT-PRIMP-V-AND)
(ADE::V-AND&)
(ADE::V-AND$NETLIST)
(ADE::V-AND$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-AND-BODY$VALUE
 (145 141 (:REWRITE DEFAULT-+-2))
 (141 141 (:REWRITE DEFAULT-+-1))
 (135 43 (:REWRITE FOLD-CONSTS-IN-+))
 (132 84 (:REWRITE DEFAULT-CDR))
 (112 70 (:REWRITE DEFAULT-CAR))
 (86 43 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (82 22 (:REWRITE ZP-OPEN))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (43 43 (:TYPE-PRESCRIPTION ADE::SIS))
 (43 43 (:TYPE-PRESCRIPTION POSP))
 (40 10 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (29 9 (:REWRITE ADE::F-GATES=B-GATES))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:REWRITE DEFAULT-<-1))
 (18 9 (:REWRITE ADE::LEN-SIS))
 (18 6 (:REWRITE ADE::FV-AND=V-AND))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 12 (:TYPE-PRESCRIPTION ADE::BVP))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 9 (:REWRITE ADE::NFIX-OF-NAT))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 3 (:REWRITE UNICITY-OF-0))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (3 3 (:DEFINITION FIX))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(ADE::V-AND$VALUE
 (256 1 (:DEFINITION ADE::SE-OCC))
 (199 52 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (192 9 (:REWRITE ADE::DISJOINT-ATOM))
 (94 10 (:DEFINITION ATOM))
 (82 9 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (65 49 (:REWRITE DEFAULT-CDR))
 (54 1 (:REWRITE ADE::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT))
 (52 52 (:TYPE-PRESCRIPTION ADE::SIS))
 (52 52 (:TYPE-PRESCRIPTION POSP))
 (49 25 (:REWRITE DEFAULT-+-2))
 (38 3 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (33 1 (:DEFINITION SUBSETP-EQUAL))
 (30 27 (:REWRITE DEFAULT-CAR))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (30 4 (:DEFINITION BINARY-APPEND))
 (28 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (27 25 (:REWRITE DEFAULT-+-1))
 (24 1 (:DEFINITION MEMBER-EQUAL))
 (14 1 (:DEFINITION ADE::V-AND-BODY))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (12 2 (:REWRITE ADE::STRIP-CARS-PAIRLIS$))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION ADE::BVP))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:TYPE-PRESCRIPTION ATOM))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE ADE::FV-AND=V-AND))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (2 2 (:REWRITE ADE::SUBSETP-TRANSITIVITY))
 (2 2 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-OR-BODY)
(ADE::V-OR*
 (12 6 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-OR*$DESTRUCTURE
 (150 75 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (75 75 (:TYPE-PRESCRIPTION POSP))
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (24 6 (:DEFINITION ADE::V-OR-BODY))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(ADE::NOT-PRIMP-V-OR)
(ADE::V-OR&)
(ADE::V-OR$NETLIST)
(ADE::V-OR$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-OR-BODY$VALUE
 (153 149 (:REWRITE DEFAULT-+-2))
 (149 149 (:REWRITE DEFAULT-+-1))
 (147 47 (:REWRITE FOLD-CONSTS-IN-+))
 (132 84 (:REWRITE DEFAULT-CDR))
 (112 70 (:REWRITE DEFAULT-CAR))
 (90 24 (:REWRITE ZP-OPEN))
 (86 43 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-AND-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (43 43 (:TYPE-PRESCRIPTION ADE::SIS))
 (43 43 (:TYPE-PRESCRIPTION POSP))
 (40 10 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (30 2 (:DEFINITION ADE::V-AND-BODY))
 (29 9 (:REWRITE ADE::F-GATES=B-GATES))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (18 9 (:REWRITE ADE::LEN-SIS))
 (18 6 (:REWRITE ADE::FV-OR=V-OR))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 12 (:TYPE-PRESCRIPTION ADE::BVP))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 9 (:REWRITE ADE::NFIX-OF-NAT))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 3 (:REWRITE UNICITY-OF-0))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (3 3 (:DEFINITION FIX))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(ADE::V-OR$VALUE
 (256 1 (:DEFINITION ADE::SE-OCC))
 (199 52 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (192 9 (:REWRITE ADE::DISJOINT-ATOM))
 (94 10 (:DEFINITION ATOM))
 (82 9 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (65 49 (:REWRITE DEFAULT-CDR))
 (54 1 (:REWRITE ADE::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT))
 (52 52 (:TYPE-PRESCRIPTION ADE::SIS))
 (52 52 (:TYPE-PRESCRIPTION POSP))
 (49 25 (:REWRITE DEFAULT-+-2))
 (38 3 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (33 1 (:DEFINITION SUBSETP-EQUAL))
 (30 27 (:REWRITE DEFAULT-CAR))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (30 4 (:DEFINITION BINARY-APPEND))
 (28 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (27 25 (:REWRITE DEFAULT-+-1))
 (24 1 (:DEFINITION MEMBER-EQUAL))
 (14 1 (:DEFINITION ADE::V-OR-BODY))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (12 2 (:REWRITE ADE::STRIP-CARS-PAIRLIS$))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION ADE::BVP))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:TYPE-PRESCRIPTION ATOM))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE ADE::FV-OR=V-OR))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (2 2 (:REWRITE ADE::SUBSETP-TRANSITIVITY))
 (2 2 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-XOR-BODY)
(ADE::V-XOR*
 (12 6 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-XOR*$DESTRUCTURE
 (150 75 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (75 75 (:TYPE-PRESCRIPTION POSP))
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (24 6 (:DEFINITION ADE::V-XOR-BODY))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(ADE::NOT-PRIMP-V-XOR)
(ADE::V-XOR&)
(ADE::V-XOR$NETLIST)
(ADE::V-XOR$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-XOR-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-XOR-BODY$VALUE
 (161 157 (:REWRITE DEFAULT-+-2))
 (159 51 (:REWRITE FOLD-CONSTS-IN-+))
 (157 157 (:REWRITE DEFAULT-+-1))
 (132 84 (:REWRITE DEFAULT-CDR))
 (112 70 (:REWRITE DEFAULT-CAR))
 (98 26 (:REWRITE ZP-OPEN))
 (86 43 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (48 2 (:REWRITE ADE::V-OR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-AND-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (43 43 (:TYPE-PRESCRIPTION ADE::SIS))
 (43 43 (:TYPE-PRESCRIPTION POSP))
 (40 10 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (30 2 (:DEFINITION ADE::V-OR-BODY))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (30 2 (:DEFINITION ADE::V-AND-BODY))
 (29 9 (:REWRITE ADE::F-GATES=B-GATES))
 (26 26 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE DEFAULT-<-1))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (18 9 (:REWRITE ADE::LEN-SIS))
 (18 6 (:REWRITE ADE::FV-XOR=V-XOR))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 12 (:TYPE-PRESCRIPTION ADE::BVP))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 9 (:TYPE-PRESCRIPTION ADE::F-XOR))
 (9 9 (:REWRITE ADE::NFIX-OF-NAT))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 3 (:REWRITE UNICITY-OF-0))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (3 3 (:DEFINITION FIX))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(ADE::V-XOR$VALUE
 (256 1 (:DEFINITION ADE::SE-OCC))
 (199 52 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (192 9 (:REWRITE ADE::DISJOINT-ATOM))
 (94 10 (:DEFINITION ATOM))
 (82 9 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (65 49 (:REWRITE DEFAULT-CDR))
 (54 1 (:REWRITE ADE::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT))
 (52 52 (:TYPE-PRESCRIPTION ADE::SIS))
 (52 52 (:TYPE-PRESCRIPTION POSP))
 (49 25 (:REWRITE DEFAULT-+-2))
 (38 3 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (33 1 (:DEFINITION SUBSETP-EQUAL))
 (30 27 (:REWRITE DEFAULT-CAR))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (30 4 (:DEFINITION BINARY-APPEND))
 (28 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (27 25 (:REWRITE DEFAULT-+-1))
 (24 1 (:DEFINITION MEMBER-EQUAL))
 (14 1 (:DEFINITION ADE::V-XOR-BODY))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (12 2 (:REWRITE ADE::STRIP-CARS-PAIRLIS$))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION ADE::BVP))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:TYPE-PRESCRIPTION ATOM))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE ADE::FV-XOR=V-XOR))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-XOR-BODY))
 (2 2 (:REWRITE ADE::SUBSETP-TRANSITIVITY))
 (2 2 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-PULLUP-BODY)
(ADE::V-PULLUP*
 (4 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-PULLUP*$DESTRUCTURE
 (60 30 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (30 30 (:TYPE-PRESCRIPTION POSP))
 (24 6 (:DEFINITION ADE::V-PULLUP-BODY))
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-V-PULLUP)
(ADE::V-PULLUP&)
(ADE::V-PULLUP$NETLIST)
(ADE::V-PULLUP$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-PULLUP-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-PULLUP-BODY$VALUE
 (142 46 (:REWRITE FOLD-CONSTS-IN-+))
 (135 133 (:REWRITE DEFAULT-+-2))
 (133 133 (:REWRITE DEFAULT-+-1))
 (90 24 (:REWRITE ZP-OPEN))
 (87 62 (:REWRITE DEFAULT-CDR))
 (74 53 (:REWRITE DEFAULT-CAR))
 (54 27 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (48 2 (:REWRITE ADE::V-XOR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-OR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-AND-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (30 2 (:DEFINITION ADE::V-XOR-BODY))
 (30 2 (:DEFINITION ADE::V-OR-BODY))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (30 2 (:DEFINITION ADE::V-AND-BODY))
 (27 27 (:TYPE-PRESCRIPTION ADE::SIS))
 (27 27 (:TYPE-PRESCRIPTION POSP))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (18 6 (:REWRITE ADE::V-PULLUP-BVP))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 12 (:TYPE-PRESCRIPTION ADE::BVP))
 (12 6 (:REWRITE ADE::LEN-SIS))
 (12 6 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-XOR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::F-PULLUP))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 6 (:REWRITE ADE::NFIX-OF-NAT))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE UNICITY-OF-0))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:DEFINITION FIX))
 )
(ADE::V-PULLUP$VALUE
 (59 1 (:DEFINITION ADE::SE-OCC))
 (49 33 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION LEN))
 (21 18 (:REWRITE DEFAULT-CAR))
 (19 10 (:REWRITE DEFAULT-+-2))
 (18 1 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (14 1 (:DEFINITION ADE::V-PULLUP-BODY))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (11 10 (:REWRITE DEFAULT-+-1))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (8 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (6 6 (:TYPE-PRESCRIPTION ADE::BVP))
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 5 (:TYPE-PRESCRIPTION PAIRLIS$))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 2 (:REWRITE ADE::V-PULLUP-BVP))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-PULLUP-BODY))
 (2 2 (:TYPE-PRESCRIPTION ADE::SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::VFT-WIRE-BODY)
(ADE::VFT-WIRE*
 (12 6 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::VFT-WIRE*$DESTRUCTURE
 (150 75 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (75 75 (:TYPE-PRESCRIPTION POSP))
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (24 6 (:DEFINITION ADE::VFT-WIRE-BODY))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(ADE::NOT-PRIMP-VFT-WIRE)
(ADE::VFT-WIRE&)
(ADE::VFT-WIRE$NETLIST)
(ADE::VFT-WIRE$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::VFT-WIRE-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::VFT-WIRE-BODY$VALUE
 (183 59 (:REWRITE FOLD-CONSTS-IN-+))
 (177 173 (:REWRITE DEFAULT-+-2))
 (173 173 (:REWRITE DEFAULT-+-1))
 (132 84 (:REWRITE DEFAULT-CDR))
 (114 30 (:REWRITE ZP-OPEN))
 (112 70 (:REWRITE DEFAULT-CAR))
 (86 43 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (48 2 (:REWRITE ADE::V-XOR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-PULLUP-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-OR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-AND-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (43 43 (:TYPE-PRESCRIPTION ADE::SIS))
 (43 43 (:TYPE-PRESCRIPTION POSP))
 (40 10 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (30 30 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-<-1))
 (30 2 (:DEFINITION ADE::V-XOR-BODY))
 (30 2 (:DEFINITION ADE::V-PULLUP-BODY))
 (30 2 (:DEFINITION ADE::V-OR-BODY))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (30 2 (:DEFINITION ADE::V-AND-BODY))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (18 9 (:REWRITE ADE::LEN-SIS))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 9 (:TYPE-PRESCRIPTION ADE::FT-WIRE))
 (9 9 (:REWRITE ADE::NFIX-OF-NAT))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-XOR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-PULLUP-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 3 (:REWRITE UNICITY-OF-0))
 (6 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (3 3 (:DEFINITION FIX))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(ADE::VFT-WIRE$VALUE
 (256 1 (:DEFINITION ADE::SE-OCC))
 (199 52 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (192 9 (:REWRITE ADE::DISJOINT-ATOM))
 (94 10 (:DEFINITION ATOM))
 (82 9 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (65 49 (:REWRITE DEFAULT-CDR))
 (54 1 (:REWRITE ADE::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT))
 (52 52 (:TYPE-PRESCRIPTION ADE::SIS))
 (52 52 (:TYPE-PRESCRIPTION POSP))
 (49 25 (:REWRITE DEFAULT-+-2))
 (38 3 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (33 1 (:DEFINITION SUBSETP-EQUAL))
 (30 27 (:REWRITE DEFAULT-CAR))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (30 4 (:DEFINITION BINARY-APPEND))
 (28 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (27 25 (:REWRITE DEFAULT-+-1))
 (24 1 (:DEFINITION MEMBER-EQUAL))
 (14 1 (:DEFINITION ADE::VFT-WIRE-BODY))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (12 2 (:REWRITE ADE::STRIP-CARS-PAIRLIS$))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION ADE::BVP))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:TYPE-PRESCRIPTION ATOM))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::VFT-WIRE-BODY))
 (2 2 (:REWRITE ADE::SUBSETP-TRANSITIVITY))
 (2 2 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-WIRE-BODY)
(ADE::V-WIRE*
 (4 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-WIRE*$DESTRUCTURE
 (60 30 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (30 30 (:TYPE-PRESCRIPTION POSP))
 (24 6 (:DEFINITION ADE::V-WIRE-BODY))
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-V-WIRE)
(ADE::V-WIRE&)
(ADE::V-WIRE$NETLIST)
(ADE::V-WIRE$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-WIRE-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-WIRE-BODY$VALUE
 (160 52 (:REWRITE FOLD-CONSTS-IN-+))
 (145 143 (:REWRITE DEFAULT-+-2))
 (143 143 (:REWRITE DEFAULT-+-1))
 (102 27 (:REWRITE ZP-OPEN))
 (76 59 (:REWRITE DEFAULT-CDR))
 (59 50 (:REWRITE DEFAULT-CAR))
 (48 2 (:REWRITE ADE::VFT-WIRE-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-XOR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-PULLUP-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-OR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-AND-BODY$VALUE))
 (46 23 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (30 2 (:DEFINITION ADE::VFT-WIRE-BODY))
 (30 2 (:DEFINITION ADE::V-XOR-BODY))
 (30 2 (:DEFINITION ADE::V-PULLUP-BODY))
 (30 2 (:DEFINITION ADE::V-OR-BODY))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (30 2 (:DEFINITION ADE::V-AND-BODY))
 (27 27 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-<-1))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (23 23 (:TYPE-PRESCRIPTION ADE::SIS))
 (23 23 (:TYPE-PRESCRIPTION POSP))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 6 (:REWRITE ADE::LEN-SIS))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::VFT-WIRE-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-XOR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-PULLUP-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 2 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 6 (:REWRITE ADE::NFIX-OF-NAT))
 (4 4 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE UNICITY-OF-0))
 (4 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:DEFINITION FIX))
 )
(ADE::V-WIRE$VALUE
 (59 1 (:DEFINITION ADE::SE-OCC))
 (49 33 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION LEN))
 (21 18 (:REWRITE DEFAULT-CAR))
 (19 10 (:REWRITE DEFAULT-+-2))
 (18 1 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (14 1 (:DEFINITION ADE::V-WIRE-BODY))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (11 10 (:REWRITE DEFAULT-+-1))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (8 2 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 5 (:TYPE-PRESCRIPTION PAIRLIS$))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:TYPE-PRESCRIPTION ADE::BVP))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION ADE::V-WIRE-BODY))
 (2 2 (:TYPE-PRESCRIPTION ADE::SIS))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 (1 1 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 )
(ADE::V-IF-BODY)
(ADE::V-IF*
 (16 8 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (8 8 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::V-IF*$DESTRUCTURE
 (150 75 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (75 75 (:TYPE-PRESCRIPTION POSP))
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (24 6 (:DEFINITION ADE::V-IF-BODY))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(ADE::NOT-PRIMP-V-IF)
(ADE::V-IF&)
(ADE::V-IF$NETLIST)
(ADE::V-IF$UNBOUND-IN-BODY
 (12 12 (:TYPE-PRESCRIPTION ADE::V-IF-BODY))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::V-IF-BODY$VALUE
 (213 69 (:REWRITE FOLD-CONSTS-IN-+))
 (209 201 (:REWRITE DEFAULT-+-2))
 (201 201 (:REWRITE DEFAULT-+-1))
 (160 111 (:REWRITE DEFAULT-CDR))
 (134 35 (:REWRITE ZP-OPEN))
 (130 86 (:REWRITE DEFAULT-CAR))
 (86 43 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (48 2 (:REWRITE ADE::VFT-WIRE-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-XOR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-WIRE-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-PULLUP-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-OR-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-NOT-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-BUF-BODY$VALUE))
 (48 2 (:REWRITE ADE::V-AND-BODY$VALUE))
 (45 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-SE-OCC))
 (43 43 (:TYPE-PRESCRIPTION ADE::SIS))
 (43 43 (:TYPE-PRESCRIPTION POSP))
 (40 10 (:REWRITE ADE::CONSP-ASSOC-EQ-VALUES))
 (35 35 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE DEFAULT-<-1))
 (30 2 (:DEFINITION ADE::VFT-WIRE-BODY))
 (30 2 (:DEFINITION ADE::V-XOR-BODY))
 (30 2 (:DEFINITION ADE::V-WIRE-BODY))
 (30 2 (:DEFINITION ADE::V-PULLUP-BODY))
 (30 2 (:DEFINITION ADE::V-OR-BODY))
 (30 2 (:DEFINITION ADE::V-NOT-BODY))
 (30 2 (:DEFINITION ADE::V-BUF-BODY))
 (30 2 (:DEFINITION ADE::V-AND-BODY))
 (26 2 (:DEFINITION MEMBER-EQUAL))
 (25 4 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (24 24 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 10 (:REWRITE ADE::F-GATES=B-GATES))
 (18 9 (:REWRITE ADE::LEN-SIS))
 (17 7 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (17 1 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-CONS))
 (12 12 (:TYPE-PRESCRIPTION ADE::SE))
 (12 2 (:DEFINITION BINARY-APPEND))
 (11 11 (:TYPE-PRESCRIPTION ADE::F-IF))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 9 (:REWRITE ADE::NFIX-OF-NAT))
 (9 3 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADE::VFT-WIRE-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-XOR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-WIRE-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-PULLUP-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-OR-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-NOT-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-BUF-BODY))
 (8 8 (:TYPE-PRESCRIPTION ADE::V-AND-BODY))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (6 6 (:TYPE-PRESCRIPTION ADE::ALL-UNBOUND-IN-BODY))
 (6 3 (:REWRITE UNICITY-OF-0))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (3 3 (:DEFINITION FIX))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 )
(ADE::V-IF$VALUE
 (85 55 (:REWRITE DEFAULT-CDR))
 (71 1 (:DEFINITION ADE::SE-OCC))
 (64 4 (:REWRITE ADE::DISJOINT-ATOM))
 (53 27 (:REWRITE DEFAULT-+-2))
 (52 35 (:REWRITE DEFAULT-CAR))
 (48 6 (:DEFINITION BINARY-APPEND))
 (41 4 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (40 5 (:REWRITE ADE::SINGLETON-ASSOC-EQ-VALUES))
 (32 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (31 3 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (30 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (30 2 (:DEFINITION ATOM))
 (29 27 (:REWRITE DEFAULT-+-1))
 (14 1 (:DEFINITION ADE::V-IF-BODY))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (11 1 (:DEFINITION ADE::DELETE-TO-EQ))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION ADE::BVP))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 1 (:REWRITE ZP-OPEN))
 (7 1 (:DEFINITION MEMBER-EQUAL))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:DEFINITION ADE::OCC-INS$INLINE))
 (4 4 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (4 2 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:DEFINITION ADE::OCC-FN$INLINE))
 (3 3 (:TYPE-PRESCRIPTION ADE::V-IF-BODY))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 1 (:REWRITE ADE::ASSOC-EQ-VALUE-CONS-2))
 (3 1 (:DEFINITION ADE::OCC-OUTS$INLINE))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (2 1 (:DEFINITION ADE::OCC-NAME$INLINE))
 )
