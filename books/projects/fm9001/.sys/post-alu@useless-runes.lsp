(FM9001::CARRY-OUT-HELP)
(FM9001::F$CARRY-OUT-HELP)
(FM9001::CARRY-OUT-HELP-OKP)
(FM9001::CARRY-OUT-HELP&)
(FM9001::CARRY-OUT-HELP$VALUE
 (547 391 (:REWRITE FM9001::F-GATES=B-GATES))
 (99 99 (:REWRITE DEFAULT-CAR))
 (90 18 (:DEFINITION FM9001::DELETE-TO-EQ))
 (84 84 (:TYPE-PRESCRIPTION BOOLEANP))
 (84 84 (:REWRITE DEFAULT-CDR))
 (54 54 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (12 4 (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
 (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND4))
 (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
 (8 8 (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
 )
(FM9001::F$CARRY-OUT-HELP=CARRY-OUT-HELP)
(FM9001::CARRY-OUT-HELP-CONGRUENCE)
(FM9001::CARRY-OUT-HELP$VALUE-ZERO
 (66 16 (:REWRITE FM9001::F-GATES=B-GATES))
 (28 28 (:TYPE-PRESCRIPTION BOOLEANP))
 (18 18 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (3 3 (:TYPE-PRESCRIPTION FM9001::F-NAND4))
 (3 3 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
 (3 1 (:REWRITE FM9001::F$CARRY-OUT-HELP=CARRY-OUT-HELP))
 )
(FM9001::OVERFLOW-HELP)
(FM9001::F$OVERFLOW-HELP
 (4 4 (:TYPE-PRESCRIPTION FM9001::F-XOR))
 )
(FM9001::OVERFLOW-HELP-OKP)
(FM9001::OVERFLOW-HELP&)
(FM9001::OVERFLOW-HELP$VALUE
 (5953 5731 (:REWRITE FM9001::F-GATES=B-GATES))
 (223 223 (:REWRITE DEFAULT-CAR))
 (200 40 (:DEFINITION FM9001::DELETE-TO-EQ))
 (192 192 (:REWRITE DEFAULT-CDR))
 (114 114 (:TYPE-PRESCRIPTION BOOLEANP))
 (54 54 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (27 27 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
 (18 18 (:TYPE-PRESCRIPTION FM9001::F-NAND))
 (12 4 (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
 (9 9 (:TYPE-PRESCRIPTION FM9001::F-NOR))
 (8 8 (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
 )
(FM9001::F$OVERFLOW-HELP=OVERFLOW-HELP)
(FM9001::OVERFLOW-HELP$VALUE-ZERO
 (728 222 (:REWRITE FM9001::F-BUF-OF-NOT-BOOLEANP))
 (3 1 (:REWRITE FM9001::F$OVERFLOW-HELP=OVERFLOW-HELP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(FM9001::V-SHIFT-RIGHT-NAMES)
(FM9001::LEN-V-SHIFT-RIGHT-NAMES
 (16 16 (:LINEAR LEN-WHEN-PREFIXP))
 (15 8 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-CDR))
 (9 8 (:REWRITE DEFAULT-+-1))
 (8 8 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (5 1 (:DEFINITION BINARY-APPEND))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (2 2 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(FM9001::ASSOC-EQ-VALUES-V-SHIFT-RIGHT
 (54 10 (:DEFINITION BINARY-APPEND))
 (43 34 (:REWRITE DEFAULT-CDR))
 (35 20 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (32 2 (:REWRITE LEN-OF-APPEND))
 (26 14 (:REWRITE DEFAULT-+-2))
 (20 8 (:REWRITE FM9001::V-THREEFIX-BVP))
 (16 16 (:LINEAR LEN-WHEN-PREFIXP))
 (16 14 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION FM9001::BVP))
 (8 8 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (3 1 (:REWRITE FM9001::FV-SHIFT-RIGHT=V-SHIFT-RIGHT))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(FM9001::SHIFT-OR-BUF-CNTL)
(FM9001::F$SHIFT-OR-BUF-CNTL)
(FM9001::SHIFT-OR-BUF-CNTL-OKP)
(FM9001::SHIFT-OR-BUF-CNTL&)
(FM9001::SHIFT-OR-BUF-CNTL$VALUE
 (232 139 (:REWRITE FM9001::F-GATES=B-GATES))
 (71 71 (:REWRITE DEFAULT-CAR))
 (60 12 (:DEFINITION FM9001::DELETE-TO-EQ))
 (54 54 (:REWRITE DEFAULT-CDR))
 (48 48 (:TYPE-PRESCRIPTION BOOLEANP))
 (27 27 (:TYPE-PRESCRIPTION FM9001::F-AND))
 (18 18 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (12 4 (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
 (8 8 (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
 )
(FM9001::F$SHIFT-OR-BUF-CNTL=SHIFT-OR-BUF-CNTL)
(FM9001::SHIFT-OR-BUF-CNTL$VALUE-ZERO
 (43 14 (:REWRITE FM9001::F-GATES=B-GATES))
 (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:TYPE-PRESCRIPTION FM9001::F-AND))
 (3 3 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (3 1 (:REWRITE FM9001::F$SHIFT-OR-BUF-CNTL=SHIFT-OR-BUF-CNTL))
 (3 1 (:DEFINITION FM9001::F-OR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(FM9001::F$SHIFT-OR-BUF)
(FM9001::LEN-F$SHIFT-OR-BUF
 (11 11 (:TYPE-PRESCRIPTION FM9001::F$SHIFT-OR-BUF-CNTL))
 (10 2 (:DEFINITION LEN))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:LINEAR LEN-WHEN-PREFIXP))
 (6 2 (:REWRITE DEFAULT-CAR))
 (6 1 (:REWRITE FM9001::FV-SHIFT-RIGHT=V-SHIFT-RIGHT))
 (6 1 (:REWRITE FM9001::FV-IF-WHEN-BVP))
 (4 3 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE FM9001::F$SHIFT-OR-BUF-CNTL=SHIFT-OR-BUF-CNTL))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(FM9001::SHIFT-OR-BUF)
(FM9001::LEN-SHIFT-OR-BUF
 (20 4 (:DEFINITION LEN))
 (19 1 (:REWRITE FM9001::V-IF-WORKS))
 (17 1 (:DEFINITION FM9001::BV2P))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:LINEAR LEN-WHEN-PREFIXP))
 (6 5 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE DEFAULT-CAR))
 (6 1 (:REWRITE FM9001::LEN-V-SHIFT-RIGHT))
 (5 5 (:TYPE-PRESCRIPTION FM9001::SHIFT-OR-BUF-CNTL))
 (4 4 (:TYPE-PRESCRIPTION FM9001::BVP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (1 1 (:TYPE-PRESCRIPTION FM9001::BV2P))
 (1 1 (:REWRITE FM9001::BVP-V-SHIFT-RIGHT))
 )
(FM9001::BVP-SHIFT-OR-BUF
 (19 1 (:REWRITE FM9001::V-IF-WORKS))
 (17 1 (:DEFINITION FM9001::BV2P))
 (10 2 (:DEFINITION LEN))
 (6 2 (:REWRITE DEFAULT-CAR))
 (6 1 (:REWRITE FM9001::LEN-V-SHIFT-RIGHT))
 (5 5 (:TYPE-PRESCRIPTION FM9001::SHIFT-OR-BUF-CNTL))
 (4 3 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION FM9001::BV2P))
 (1 1 (:REWRITE FM9001::BVP-V-SHIFT-RIGHT))
 )
(FM9001::F$SHIFT-OR-BUF=SHIFT-OR-BUF
 (20 4 (:DEFINITION LEN))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(FM9001::SHIFT-OR-BUF-IS-BUF
 (44 44 (:TYPE-PRESCRIPTION BOOLEANP))
 (40 8 (:DEFINITION LEN))
 (16 8 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-CDR))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(FM9001::SHIFT-OR-BUF-IS-ASR
 (80 4 (:DEFINITION NTH))
 (32 4 (:REWRITE ZP-OPEN))
 (24 14 (:REWRITE DEFAULT-+-2))
 (20 4 (:DEFINITION LEN))
 (16 4 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE NTH-WHEN-PREFIXP))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE FM9001::SHIFT-OR-BUF-IS-BUF))
 )
(FM9001::SHIFT-OR-BUF-IS-ROR
 (38 1 (:REWRITE FM9001::SHIFT-OR-BUF-IS-ASR))
 (20 1 (:DEFINITION NTH))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (15 3 (:DEFINITION LEN))
 (11 6 (:REWRITE DEFAULT-+-2))
 (8 4 (:TYPE-PRESCRIPTION FM9001::NTH-OF-BVP-IS-BOOLEANP))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE FM9001::SHIFT-OR-BUF-IS-BUF))
 (1 1 (:REWRITE NTH-WHEN-PREFIXP))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(FM9001::SHIFT-OR-BUF-IS-LSR
 (38 1 (:REWRITE FM9001::SHIFT-OR-BUF-IS-ASR))
 (20 1 (:DEFINITION NTH))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (15 3 (:DEFINITION LEN))
 (11 6 (:REWRITE DEFAULT-+-2))
 (8 4 (:TYPE-PRESCRIPTION FM9001::NTH-OF-BVP-IS-BOOLEANP))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:REWRITE FM9001::SHIFT-OR-BUF-IS-ROR))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE FM9001::SHIFT-OR-BUF-IS-BUF))
 (1 1 (:REWRITE NTH-WHEN-PREFIXP))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(FM9001::TV-SHIFT-OR-BUF*)
(FM9001::TV-SHIFT-OR-BUF*$DESTRUCTURE
 (324 18 (:DEFINITION BINARY-APPEND))
 (234 36 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (88 34 (:REWRITE DEFAULT-CDR))
 (59 23 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE FM9001::TREE-SIZE-ATOM))
 )
(FM9001::TV-SHIFT-OR-BUF&)
(FM9001::TV-SHIFT-OR-BUF$NETLIST)
(FM9001::TV-SHIFT-OR-BUF$VALUE-AUX
 (591 202 (:REWRITE FM9001::F-GATES=B-GATES))
 (243 202 (:REWRITE DEFAULT-CDR))
 (209 19 (:DEFINITION FM9001::DELETE-TO-EQ))
 (159 123 (:REWRITE DEFAULT-CAR))
 (153 17 (:DEFINITION FM9001::V-THREEFIX))
 (144 7 (:DEFINITION PAIRLIS$))
 (117 39 (:REWRITE FM9001::V-THREEFIX-BVP))
 (108 108 (:TYPE-PRESCRIPTION FM9001::F-AND))
 (108 108 (:TYPE-PRESCRIPTION FM9001::BVP))
 (97 52 (:REWRITE DEFAULT-+-2))
 (90 66 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (76 19 (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
 (75 75 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (59 52 (:REWRITE DEFAULT-+-1))
 (45 15 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (39 3 (:REWRITE FM9001::SINGLETON-ASSOC-EQ-VALUES))
 (38 38 (:TYPE-PRESCRIPTION FM9001::SI))
 (38 38 (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
 (27 27 (:REWRITE FM9001::TREE-SIZE-ATOM))
 (24 4 (:REWRITE FM9001::FV-SHIFT-RIGHT=V-SHIFT-RIGHT))
 (22 11 (:REWRITE DEFAULT-<-1))
 (20 20 (:LINEAR LEN-WHEN-PREFIXP))
 (19 19 (:REWRITE DEFAULT-SYMBOL-NAME))
 (12 12 (:TYPE-PRESCRIPTION FM9001::F-OR))
 (12 3 (:REWRITE FM9001::ASSOC-EQ-VALUES-ATOM))
 (11 11 (:REWRITE DEFAULT-<-2))
 (10 10 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (6 1 (:REWRITE CAR-OF-APPEND))
 (4 2 (:REWRITE REPEAT-WHEN-ZP))
 (4 2 (:REWRITE CONSP-OF-REPEAT))
 (4 1 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 )
(FM9001::NOT-PRIMP-TV-SHIFT-OR-BUF)
(FM9001::TV-SHIFT-OR-BUF$VALUE
 (972 4 (:DEFINITION FM9001::SE))
 (616 4 (:DEFINITION FM9001::SE-PRIMP-APPLY))
 (516 231 (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
 (383 166 (:REWRITE FM9001::F-GATES=B-GATES))
 (363 249 (:REWRITE DEFAULT-CDR))
 (293 199 (:REWRITE DEFAULT-CAR))
 (209 19 (:DEFINITION FM9001::DELETE-TO-EQ))
 (130 130 (:TYPE-PRESCRIPTION BOOLEANP))
 (117 7 (:REWRITE LEN-OF-APPEND))
 (103 54 (:REWRITE DEFAULT-+-2))
 (68 2 (:REWRITE FM9001::TV-IF$VALUE))
 (63 63 (:TYPE-PRESCRIPTION FM9001::F-AND))
 (60 16 (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
 (59 54 (:REWRITE DEFAULT-+-1))
 (46 46 (:TYPE-PRESCRIPTION PAIRLIS$))
 (42 42 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (40 40 (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
 (32 32 (:LINEAR LEN-WHEN-PREFIXP))
 (29 12 (:REWRITE FM9001::ASSOC-EQ-VALUES-ATOM))
 (27 27 (:REWRITE DEFAULT-SYMBOL-NAME))
 (24 8 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (24 4 (:REWRITE FM9001::DISJOINT-ATOM))
 (23 3 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-2))
 (21 3 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-1))
 (20 5 (:REWRITE COMMUTATIVITY-OF-+))
 (19 4 (:REWRITE FM9001::FV-SHIFT-RIGHT=V-SHIFT-RIGHT))
 (19 4 (:REWRITE FM9001::FV-IF-WHEN-BVP))
 (18 18 (:REWRITE FM9001::TREE-SIZE-ATOM))
 (16 16 (:TYPE-PRESCRIPTION FM9001::BVP))
 (16 2 (:REWRITE COMMUTATIVITY-2-OF-+))
 (12 4 (:REWRITE FM9001::NET-SYNTAX-OKP-DELETE-TO-EQ-NETLIST))
 (12 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (11 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 6 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:TYPE-PRESCRIPTION FM9001::DISJOINT))
 (7 3 (:REWRITE FM9001::F$SHIFT-OR-BUF-CNTL=SHIFT-OR-BUF-CNTL))
 (6 4 (:REWRITE FM9001::DISJOINT-SIS-DIFF-SYMS))
 (3 3 (:REWRITE FM9001::SUBSETP-TRANSITIVITY))
 (3 1 (:REWRITE FM9001::F$SHIFT-OR-BUF=SHIFT-OR-BUF))
 )
(FM9001::TV-SHIFT-OR-BUF$VALUE-ZERO
 (539 280 (:REWRITE DEFAULT-+-2))
 (301 280 (:REWRITE DEFAULT-+-1))
 (288 288 (:REWRITE DEFAULT-CDR))
 (136 23 (:DEFINITION BINARY-APPEND))
 (114 114 (:TYPE-PRESCRIPTION FM9001::V-THREEFIX))
 (112 46 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (112 43 (:REWRITE FM9001::F-GATES=B-GATES))
 (94 94 (:LINEAR LEN-WHEN-PREFIXP))
 (70 70 (:REWRITE DEFAULT-CAR))
 (67 67 (:REWRITE FM9001::TREE-SIZE-ATOM))
 (44 44 (:REWRITE FM9001::OPEN-V-THREEFIX))
 (30 1 (:REWRITE FM9001::FV-IF-WHEN-BOOLEANP-C))
 (24 24 (:TYPE-PRESCRIPTION FM9001::F-AND))
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (6 6 (:TYPE-PRESCRIPTION FM9001::F-NOT))
 (6 1 (:REWRITE FM9001::FV-SHIFT-RIGHT=V-SHIFT-RIGHT))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (4 2 (:REWRITE FM9001::F$SHIFT-OR-BUF-CNTL=SHIFT-OR-BUF-CNTL))
 (3 3 (:TYPE-PRESCRIPTION FM9001::F-OR))
 (3 1 (:REWRITE FM9001::FV-IF-WHEN-BVP))
 (3 1 (:REWRITE FM9001::F$SHIFT-OR-BUF=SHIFT-OR-BUF))
 )
