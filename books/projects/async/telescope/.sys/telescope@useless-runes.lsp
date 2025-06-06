(ADE::TELESCOPE$DATA-INS-LEN
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ADE::TELESCOPE$INS-LEN)
(ADE::TELESCOPE*
 (10 10 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::TELESCOPE*$DESTRUCTURE
 (66 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (60 60 (:TYPE-PRESCRIPTION POSP))
 (60 6 (:DEFINITION BINARY-APPEND))
 (16 16 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-TELESCOPE)
(ADE::TELESCOPE$NETLIST)
(ADE::TELESCOPE&)
(ADE::CHECK-TELESCOPE$NETLIST-64)
(ADE::TELESCOPE$VALID-ST)
(ADE::TELESCOPE$DATA-IN
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION ADE::BVP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ADE::LEN-TELESCOPE$DATA-IN)
(ADE::TELESCOPE$IN-ACT
 (10 5 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (5 5 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::TELESCOPE$IN-ACT-INACTIVE
 (20 2 (:DEFINITION NTHCDR))
 (12 2 (:REWRITE COMMUTATIVITY-OF-+))
 (11 11 (:REWRITE NTH-WHEN-PREFIXP))
 (10 2 (:REWRITE ADE::NFIX-OF-NAT))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE ADE::F-GATES=B-GATES))
 (6 2 (:DEFINITION NATP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::TELESCOPE$OUT-ACT
 (10 5 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (5 5 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::TELESCOPE$OUT-ACT-INACTIVE
 (20 2 (:DEFINITION NTHCDR))
 (12 2 (:REWRITE COMMUTATIVITY-OF-+))
 (11 11 (:REWRITE NTH-WHEN-PREFIXP))
 (10 2 (:REWRITE ADE::NFIX-OF-NAT))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE ADE::F-GATES=B-GATES))
 (6 2 (:DEFINITION NATP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(ADE::TELESCOPE$DATA-OUT)
(ADE::LEN-TELESCOPE$DATA-OUT)
(ADE::BVP-TELESCOPE$DATA-OUT)
(ADE::TELESCOPE$OUTPUTS)
(ADE::TELESCOPE$VALUE
 (308 2 (:REWRITE ADE::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT))
 (181 91 (:REWRITE DEFAULT-+-2))
 (128 8 (:REWRITE ADE::DISJOINT-ATOM))
 (94 91 (:REWRITE DEFAULT-+-1))
 (82 8 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (80 16 (:DEFINITION BINARY-APPEND))
 (72 8 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (72 8 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (60 4 (:DEFINITION ATOM))
 (30 30 (:TYPE-PRESCRIPTION PAIRLIS$))
 (30 30 (:LINEAR LEN-WHEN-PREFIXP))
 (29 1 (:REWRITE PREFIXP-OF-APPEND-ARG1))
 (21 7 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (20 10 (:REWRITE DEFAULT-<-2))
 (18 18 (:TYPE-PRESCRIPTION ADE::DISJOINT))
 (18 18 (:REWRITE NTH-WHEN-PREFIXP))
 (17 1 (:REWRITE ADE::TELESCOPE$OUT-ACT-INACTIVE))
 (17 1 (:REWRITE ADE::TELESCOPE$IN-ACT-INACTIVE))
 (15 15 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (14 14 (:TYPE-PRESCRIPTION ADE::BVP))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (11 10 (:REWRITE DEFAULT-<-1))
 (11 7 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (11 7 (:REWRITE ADE::F-BUF-OF-3VP))
 (11 5 (:REWRITE ADE::V-THREEFIX-BVP))
 (9 3 (:REWRITE ADE::CAR-V-THREEFIX))
 (8 8 (:REWRITE ADE::DISJOINT-SIS-DIFF-SYMS))
 (8 3 (:REWRITE TAKE-WHEN-ATOM))
 (8 2 (:DEFINITION TRUE-LISTP))
 (7 7 (:TYPE-PRESCRIPTION ADE::3VP))
 (6 3 (:DEFINITION ADE::3V-FIX))
 (5 5 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (4 4 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (4 4 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 (1 1 (:REWRITE CONSP-OF-APPEND))
 )
(ADE::TELESCOPE$STEP
 (1 1 (:TYPE-PRESCRIPTION ADE::F-SR))
 )
(ADE::TELESCOPE$STATE
 (228 114 (:REWRITE DEFAULT-+-2))
 (128 28 (:DEFINITION BINARY-APPEND))
 (128 8 (:REWRITE ADE::DISJOINT-ATOM))
 (116 114 (:REWRITE DEFAULT-+-1))
 (82 8 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (72 8 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (72 8 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (60 60 (:TYPE-PRESCRIPTION PAIRLIS$))
 (60 4 (:DEFINITION ATOM))
 (42 14 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (26 26 (:LINEAR LEN-WHEN-PREFIXP))
 (24 8 (:REWRITE ADE::CAR-V-THREEFIX))
 (20 20 (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
 (19 19 (:REWRITE NTH-WHEN-PREFIXP))
 (19 13 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (19 13 (:REWRITE ADE::F-BUF-OF-3VP))
 (17 1 (:REWRITE ADE::TELESCOPE$OUT-ACT-INACTIVE))
 (17 1 (:REWRITE ADE::TELESCOPE$IN-ACT-INACTIVE))
 (16 8 (:REWRITE DEFAULT-<-2))
 (16 8 (:DEFINITION ADE::3V-FIX))
 (14 14 (:TYPE-PRESCRIPTION ADE::BVP))
 (14 14 (:TYPE-PRESCRIPTION ADE::3VP))
 (14 8 (:REWRITE ADE::V-THREEFIX-BVP))
 (13 13 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (13 13 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (12 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 2 (:DEFINITION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (4 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE TAKE-WHEN-ATOM))
 (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (2 2 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (2 2 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 1 (:REWRITE ADE::ASSOC-EQ-VALUES-UPDATE-ALIST-NOT-MEMBER))
 )
(ADE::TELESCOPE$INPUT-FORMAT)
(ADE::BOOLEANP-TELESCOPE$IN-ACT
 (53 53 (:REWRITE NTH-WHEN-PREFIXP))
 (38 7 (:DEFINITION NTHCDR))
 (36 6 (:REWRITE ADE::TELESCOPE$IN-ACT-INACTIVE))
 (27 9 (:REWRITE ADE::F-GATES=B-GATES))
 (26 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 2 (:REWRITE ADE::LEN-NTHCDR))
 (20 16 (:REWRITE DEFAULT-+-2))
 (20 4 (:DEFINITION LEN))
 (18 3 (:REWRITE COMMUTATIVITY-OF-+))
 (18 2 (:DEFINITION TRUE-LISTP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (15 15 (:REWRITE DEFAULT-CDR))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (9 3 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (9 3 (:REWRITE ADE::F-BUF-OF-3VP))
 (8 6 (:REWRITE DEFAULT-<-1))
 (8 4 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (6 6 (:TYPE-PRESCRIPTION ADE::3VP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE ADE::BVP-NTHCDR))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::BOOLEANP-TELESCOPE$OUT-ACT
 (53 53 (:REWRITE NTH-WHEN-PREFIXP))
 (38 7 (:DEFINITION NTHCDR))
 (36 6 (:REWRITE ADE::TELESCOPE$OUT-ACT-INACTIVE))
 (27 9 (:REWRITE ADE::F-GATES=B-GATES))
 (26 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 2 (:REWRITE ADE::LEN-NTHCDR))
 (20 16 (:REWRITE DEFAULT-+-2))
 (20 4 (:DEFINITION LEN))
 (18 3 (:REWRITE COMMUTATIVITY-OF-+))
 (18 2 (:DEFINITION TRUE-LISTP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (15 15 (:REWRITE DEFAULT-CDR))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (9 3 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (9 3 (:REWRITE ADE::F-BUF-OF-3VP))
 (8 6 (:REWRITE DEFAULT-<-1))
 (8 4 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (6 6 (:TYPE-PRESCRIPTION ADE::3VP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE ADE::BVP-NTHCDR))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(ADE::TELESCOPE$VALID-ST-PRESERVED
 (272 272 (:REWRITE NTH-WHEN-PREFIXP))
 (174 174 (:TYPE-PRESCRIPTION BOOLEANP))
 (150 31 (:DEFINITION NTHCDR))
 (135 45 (:REWRITE ADE::F-GATES=B-GATES))
 (90 15 (:REWRITE ADE::TELESCOPE$OUT-ACT-INACTIVE))
 (90 15 (:REWRITE ADE::TELESCOPE$IN-ACT-INACTIVE))
 (66 11 (:REWRITE COMMUTATIVITY-OF-+))
 (52 48 (:REWRITE DEFAULT-+-2))
 (51 51 (:REWRITE DEFAULT-CDR))
 (48 48 (:REWRITE DEFAULT-+-1))
 (45 15 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (45 15 (:REWRITE ADE::F-BUF-OF-3VP))
 (33 11 (:REWRITE FOLD-CONSTS-IN-+))
 (30 30 (:TYPE-PRESCRIPTION ADE::3VP))
 (26 4 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 2 (:REWRITE ADE::LEN-NTHCDR))
 (20 4 (:DEFINITION LEN))
 (18 2 (:DEFINITION TRUE-LISTP))
 (16 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-<-2))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (8 4 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (6 2 (:REWRITE ADE::BVP-NTHCDR))
 (3 1 (:DEFINITION NATP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
