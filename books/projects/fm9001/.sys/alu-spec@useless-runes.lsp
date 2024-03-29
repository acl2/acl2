(FM9001::CVZBV)
(C)
(V)
(FM9001::BV)
(N
 (10 5 (:TYPE-PRESCRIPTION FM9001::BOOLEANP-V-NEGP))
 (5 5 (:TYPE-PRESCRIPTION FM9001::BVP))
 )
(FM9001::ZB)
(FM9001::BOOLEANP-N)
(FM9001::BOOLEANP-ZP-CVZBV
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(FM9001::BOOLEANP-BVP-CVZBV
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(FM9001::BVP-CVZBV
 (47 47 (:REWRITE DEFAULT-CDR))
 (19 19 (:REWRITE DEFAULT-CAR))
 )
(FM9001::CVZBV-V-ROR
 (11 3 (:TYPE-PRESCRIPTION FM9001::NTH-OF-BVP-IS-BOOLEANP))
 (5 3 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (3 3 (:TYPE-PRESCRIPTION FM9001::BVP))
 )
(FM9001::CVZBV-V-ADDER)
(FM9001::CVZBV-V-LSL)
(FM9001::CVZBV-V-SUBTRACTER)
(FM9001::CVZBV-INC
 (106 14 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (64 6 (:REWRITE FM9001::BVP-CVZBV))
 (40 20 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (40 5 (:REWRITE ZP-OPEN))
 (21 13 (:REWRITE DEFAULT-+-2))
 (20 20 (:TYPE-PRESCRIPTION FM9001::BVP))
 (13 13 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-<-1))
 )
(FM9001::CVZBV-NEG
 (106 14 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (64 6 (:REWRITE FM9001::BVP-CVZBV))
 (40 20 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (40 5 (:REWRITE ZP-OPEN))
 (21 13 (:REWRITE DEFAULT-+-2))
 (20 20 (:TYPE-PRESCRIPTION FM9001::BVP))
 (13 13 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-<-1))
 )
(FM9001::CVZBV-DEC
 (106 14 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (64 6 (:REWRITE FM9001::BVP-CVZBV))
 (40 20 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (40 5 (:REWRITE ZP-OPEN))
 (21 13 (:REWRITE DEFAULT-+-2))
 (20 20 (:TYPE-PRESCRIPTION FM9001::BVP))
 (13 13 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-<-1))
 )
(FM9001::CVZBV-V-NOT)
(FM9001::CVZBV-V-ASR
 (11 3 (:TYPE-PRESCRIPTION FM9001::NTH-OF-BVP-IS-BOOLEANP))
 (5 3 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (3 3 (:TYPE-PRESCRIPTION FM9001::BVP))
 )
(FM9001::CVZBV-V-LSR
 (5 3 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (3 3 (:TYPE-PRESCRIPTION FM9001::BVP))
 )
(FM9001::V-ALU)
(FM9001::TRUE-LISTP-V-ALU
 (2166 38 (:DEFINITION TAKE))
 (1912 839 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (1576 76 (:REWRITE TAKE-OF-TOO-MANY))
 (1477 265 (:DEFINITION LEN))
 (1146 76 (:REWRITE TAKE-OF-LEN-FREE))
 (1097 635 (:REWRITE DEFAULT-+-2))
 (635 635 (:REWRITE DEFAULT-+-1))
 (614 373 (:REWRITE DEFAULT-<-2))
 (596 60 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (591 416 (:REWRITE DEFAULT-CDR))
 (558 558 (:TYPE-PRESCRIPTION BOOLEANP))
 (522 9 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (468 52 (:REWRITE CONSP-OF-TAKE))
 (445 373 (:REWRITE DEFAULT-<-1))
 (422 4 (:DEFINITION TRUE-LISTP))
 (398 4 (:REWRITE FM9001::BVP-CVZBV))
 (237 150 (:REWRITE DEFAULT-CAR))
 (228 76 (:REWRITE TAKE-WHEN-ATOM))
 (182 26 (:REWRITE CAR-OF-TAKE))
 (94 94 (:TYPE-PRESCRIPTION NFIX))
 (46 2 (:REWRITE FM9001::V-BUF-WORKS))
 (35 32 (:REWRITE FM9001::NTH-V-NOT))
 (33 33 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (3 3 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 )
(FM9001::BOOLEANP-C-V-ALU
 (3230 1615 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (1748 38 (:DEFINITION TAKE))
 (1562 282 (:DEFINITION LEN))
 (1496 136 (:REWRITE FM9001::BVP-CVZBV))
 (1330 76 (:REWRITE TAKE-OF-TOO-MANY))
 (1224 68 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (1187 1187 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1105 51 (:DEFINITION FM9001::BVP))
 (976 654 (:REWRITE DEFAULT-+-2))
 (960 76 (:REWRITE TAKE-OF-LEN-FREE))
 (782 34 (:DEFINITION TRUE-LISTP))
 (654 654 (:REWRITE DEFAULT-+-1))
 (654 515 (:REWRITE DEFAULT-CDR))
 (524 60 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (319 261 (:REWRITE DEFAULT-<-2))
 (292 196 (:REWRITE DEFAULT-CAR))
 (261 261 (:REWRITE DEFAULT-<-1))
 (228 76 (:REWRITE TAKE-WHEN-ATOM))
 (182 26 (:REWRITE CAR-OF-TAKE))
 (94 94 (:TYPE-PRESCRIPTION NFIX))
 (52 52 (:REWRITE CONSP-OF-TAKE))
 (35 32 (:REWRITE FM9001::NTH-V-NOT))
 (33 33 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (3 3 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 )
(FM9001::BOOLEANP-V-V-ALU
 (2846 1423 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (1748 38 (:DEFINITION TAKE))
 (1562 282 (:DEFINITION LEN))
 (1330 76 (:REWRITE TAKE-OF-TOO-MANY))
 (976 654 (:REWRITE DEFAULT-+-2))
 (960 76 (:REWRITE TAKE-OF-LEN-FREE))
 (816 816 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (654 654 (:REWRITE DEFAULT-+-1))
 (635 464 (:REWRITE DEFAULT-CDR))
 (524 60 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (442 51 (:REWRITE FM9001::BVP-CVZBV))
 (319 261 (:REWRITE DEFAULT-<-2))
 (306 34 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (273 145 (:REWRITE DEFAULT-CAR))
 (261 261 (:REWRITE DEFAULT-<-1))
 (238 17 (:DEFINITION TRUE-LISTP))
 (228 76 (:REWRITE TAKE-WHEN-ATOM))
 (182 26 (:REWRITE CAR-OF-TAKE))
 (94 94 (:TYPE-PRESCRIPTION NFIX))
 (52 52 (:REWRITE CONSP-OF-TAKE))
 (35 32 (:REWRITE FM9001::NTH-V-NOT))
 (33 33 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (3 3 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 )
(FM9001::BOOLEANP-ZB-V-ALU
 (2166 38 (:DEFINITION TAKE))
 (1664 832 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (1576 76 (:REWRITE TAKE-OF-TOO-MANY))
 (1477 265 (:DEFINITION LEN))
 (1146 76 (:REWRITE TAKE-OF-LEN-FREE))
 (1097 635 (:REWRITE DEFAULT-+-2))
 (691 448 (:REWRITE DEFAULT-CDR))
 (635 635 (:REWRITE DEFAULT-+-1))
 (614 373 (:REWRITE DEFAULT-<-2))
 (596 60 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (468 52 (:REWRITE CONSP-OF-TAKE))
 (445 373 (:REWRITE DEFAULT-<-1))
 (324 167 (:REWRITE DEFAULT-CAR))
 (284 284 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (228 76 (:REWRITE TAKE-WHEN-ATOM))
 (182 26 (:REWRITE CAR-OF-TAKE))
 (94 94 (:TYPE-PRESCRIPTION NFIX))
 (46 2 (:REWRITE FM9001::V-BUF-WORKS))
 (35 32 (:REWRITE FM9001::NTH-V-NOT))
 (33 33 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (32 2 (:REWRITE FM9001::BVP-CVZBV))
 (18 2 (:DEFINITION TRUE-LISTP))
 (16 4 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 )
(FM9001::BVP-BV-V-ALU
 (2166 38 (:DEFINITION TAKE))
 (1576 76 (:REWRITE TAKE-OF-TOO-MANY))
 (1477 265 (:DEFINITION LEN))
 (1146 76 (:REWRITE TAKE-OF-LEN-FREE))
 (1100 637 (:REWRITE DEFAULT-+-2))
 (965 965 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (781 482 (:REWRITE DEFAULT-CDR))
 (772 70 (:REWRITE FM9001::BVP-CVZBV))
 (637 637 (:REWRITE DEFAULT-+-1))
 (616 374 (:REWRITE DEFAULT-<-2))
 (596 60 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (470 470 (:TYPE-PRESCRIPTION FM9001::CVZBV))
 (468 52 (:REWRITE CONSP-OF-TAKE))
 (446 374 (:REWRITE DEFAULT-<-1))
 (436 36 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (364 18 (:DEFINITION TRUE-LISTP))
 (238 151 (:REWRITE DEFAULT-CAR))
 (228 76 (:REWRITE TAKE-WHEN-ATOM))
 (182 26 (:REWRITE CAR-OF-TAKE))
 (110 110 (:TYPE-PRESCRIPTION FM9001::V-SHIFT-RIGHT))
 (94 94 (:TYPE-PRESCRIPTION NFIX))
 (35 32 (:REWRITE FM9001::NTH-V-NOT))
 (33 33 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (22 22 (:TYPE-PRESCRIPTION FM9001::V-XOR))
 (22 22 (:TYPE-PRESCRIPTION FM9001::V-OR))
 (22 22 (:TYPE-PRESCRIPTION FM9001::V-AND))
 (3 3 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 )
(FM9001::BVP-V-ALU
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(FM9001::LEN-CVZBV-ADDER
 (456 8 (:DEFINITION TAKE))
 (323 12 (:DEFINITION NTH))
 (268 16 (:REWRITE TAKE-OF-TOO-MANY))
 (196 16 (:REWRITE TAKE-OF-LEN-FREE))
 (182 103 (:REWRITE DEFAULT-+-2))
 (176 24 (:REWRITE ZP-OPEN))
 (103 103 (:REWRITE DEFAULT-+-1))
 (93 57 (:REWRITE DEFAULT-<-2))
 (92 68 (:REWRITE DEFAULT-CDR))
 (92 28 (:DEFINITION NOT))
 (72 8 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (72 8 (:REWRITE CONSP-OF-TAKE))
 (66 57 (:REWRITE DEFAULT-<-1))
 (58 29 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (48 16 (:REWRITE TAKE-WHEN-ATOM))
 (33 20 (:REWRITE DEFAULT-CAR))
 (28 4 (:REWRITE CAR-OF-TAKE))
 (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 16 (:TYPE-PRESCRIPTION NFIX))
 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 3 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 )
(FM9001::LEN-CVZBV-SUBTRACTER
 (5586 98 (:DEFINITION TAKE))
 (2526 196 (:REWRITE TAKE-OF-TOO-MANY))
 (1892 196 (:REWRITE TAKE-OF-LEN-FREE))
 (1652 927 (:REWRITE DEFAULT-+-2))
 (1246 623 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (927 927 (:REWRITE DEFAULT-+-1))
 (899 669 (:REWRITE DEFAULT-CDR))
 (812 494 (:REWRITE DEFAULT-<-2))
 (588 196 (:REWRITE TAKE-WHEN-ATOM))
 (546 494 (:REWRITE DEFAULT-<-1))
 (426 426 (:TYPE-PRESCRIPTION BOOLEANP))
 (396 44 (:REWRITE CONSP-OF-TAKE))
 (360 36 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (317 180 (:REWRITE DEFAULT-CAR))
 (197 197 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (154 22 (:REWRITE CAR-OF-TAKE))
 (138 138 (:TYPE-PRESCRIPTION NFIX))
 (48 48 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (26 26 (:REWRITE FM9001::NTH-V-NOT))
 (2 2 (:TYPE-PRESCRIPTION FM9001::CVZBV))
 )
(FM9001::LEN-V-ALU
 (20292 356 (:DEFINITION TAKE))
 (9514 712 (:REWRITE TAKE-OF-TOO-MANY))
 (7110 712 (:REWRITE TAKE-OF-LEN-FREE))
 (6340 3505 (:REWRITE DEFAULT-+-2))
 (4656 2328 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (3505 3505 (:REWRITE DEFAULT-+-1))
 (3427 2613 (:REWRITE DEFAULT-CDR))
 (2862 1758 (:REWRITE DEFAULT-<-2))
 (2136 712 (:REWRITE TAKE-WHEN-ATOM))
 (2006 1758 (:REWRITE DEFAULT-<-1))
 (1580 156 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (1548 1548 (:TYPE-PRESCRIPTION BOOLEANP))
 (1152 128 (:REWRITE CONSP-OF-TAKE))
 (1091 612 (:REWRITE DEFAULT-CAR))
 (800 800 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (498 498 (:TYPE-PRESCRIPTION NFIX))
 (448 64 (:REWRITE CAR-OF-TAKE))
 (206 206 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (104 16 (:REWRITE FM9001::V-BUF-WORKS))
 (84 54 (:REWRITE FM9001::NTH-V-NOT))
 (64 4 (:REWRITE FM9001::BVP-CVZBV))
 (36 4 (:DEFINITION TRUE-LISTP))
 (32 8 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (30 30 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 (2 2 (:TYPE-PRESCRIPTION FM9001::CVZBV))
 )
(FM9001::LEN-BV
 (38 19 (:REWRITE DEFAULT-+-2))
 (27 27 (:REWRITE DEFAULT-CDR))
 (19 19 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(FM9001::BVP-BV
 (535 47 (:REWRITE FM9001::BVP-CVZBV))
 (403 30 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (393 15 (:DEFINITION TRUE-LISTP))
 (184 184 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (113 113 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE DEFAULT-CAR))
 )
(FM9001::UNARY-OP-CODE-P)
(FM9001::BOOLEANP-UNARY-OP-CODE-P)
(FM9001::V-ALU-1)
(FM9001::BVP-V-ALU-1
 (31 31 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 3 (:REWRITE FM9001::BVP-CVZBV))
 (18 2 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (14 1 (:DEFINITION TRUE-LISTP))
 (5 1 (:DEFINITION LEN))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(FM9001::LEN-V-ALU-1
 (10 2 (:DEFINITION LEN))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(FM9001::UNARY-OP-CODE-P->V-ALU=V-ALU-1
 (684 12 (:DEFINITION TAKE))
 (568 24 (:REWRITE TAKE-OF-TOO-MANY))
 (418 74 (:DEFINITION LEN))
 (416 58 (:REWRITE ZP-OPEN))
 (412 24 (:REWRITE TAKE-OF-LEN-FREE))
 (338 198 (:REWRITE DEFAULT-+-2))
 (248 24 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (236 154 (:REWRITE DEFAULT-<-2))
 (216 24 (:REWRITE CONSP-OF-TAKE))
 (204 102 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (202 154 (:REWRITE DEFAULT-<-1))
 (198 198 (:REWRITE DEFAULT-+-1))
 (178 124 (:REWRITE DEFAULT-CDR))
 (100 28 (:REWRITE FOLD-CONSTS-IN-+))
 (92 4 (:REWRITE FM9001::V-BUF-WORKS))
 (84 12 (:REWRITE CAR-OF-TAKE))
 (82 52 (:REWRITE DEFAULT-CAR))
 (72 24 (:REWRITE TAKE-WHEN-ATOM))
 (70 70 (:TYPE-PRESCRIPTION BOOLEANP))
 (64 4 (:REWRITE FM9001::BVP-CVZBV))
 (52 52 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION NFIX))
 (36 4 (:DEFINITION TRUE-LISTP))
 (32 8 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (22 22 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 (14 8 (:REWRITE FM9001::NTH-V-NOT))
 (6 6 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 )
(FM9001::ALU-INC-OP)
(FM9001::BVP-ALU-INC-OP)
(FM9001::LEN-ALU-INC-OP)
(FM9001::BV-V-ALU-ALU-INC-OP
 (171 3 (:DEFINITION TAKE))
 (141 5 (:DEFINITION NTH))
 (138 6 (:REWRITE TAKE-OF-TOO-MANY))
 (117 21 (:DEFINITION LEN))
 (99 6 (:REWRITE TAKE-OF-LEN-FREE))
 (76 43 (:REWRITE DEFAULT-+-2))
 (72 10 (:REWRITE ZP-OPEN))
 (54 6 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (45 32 (:REWRITE DEFAULT-CDR))
 (43 43 (:REWRITE DEFAULT-+-1))
 (43 27 (:REWRITE DEFAULT-<-2))
 (40 12 (:DEFINITION NOT))
 (36 4 (:REWRITE CONSP-OF-TAKE))
 (34 27 (:REWRITE DEFAULT-<-1))
 (22 11 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (18 6 (:REWRITE TAKE-WHEN-ATOM))
 (14 8 (:REWRITE DEFAULT-CAR))
 (14 4 (:REWRITE FOLD-CONSTS-IN-+))
 (14 2 (:REWRITE CAR-OF-TAKE))
 (8 8 (:TYPE-PRESCRIPTION NFIX))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 )
(FM9001::ALU-DEC-OP)
(FM9001::BVP-ALU-DEC-OP)
(FM9001::LEN-ALU-DEC-OP)
(FM9001::BV-V-ALU-ALU-DEC-OP
 (171 3 (:DEFINITION TAKE))
 (165 6 (:DEFINITION NTH))
 (147 6 (:REWRITE TAKE-OF-TOO-MANY))
 (108 6 (:REWRITE TAKE-OF-LEN-FREE))
 (80 11 (:REWRITE ZP-OPEN))
 (72 6 (:REWRITE FM9001::LEN-OF-V-ADDER))
 (59 40 (:REWRITE DEFAULT-<-1))
 (57 40 (:REWRITE DEFAULT-<-2))
 (57 9 (:DEFINITION LEN))
 (55 33 (:REWRITE DEFAULT-+-2))
 (43 13 (:DEFINITION NOT))
 (40 20 (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
 (36 4 (:REWRITE CONSP-OF-TAKE))
 (34 21 (:REWRITE DEFAULT-CDR))
 (33 33 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE TAKE-WHEN-ATOM))
 (18 5 (:REWRITE FOLD-CONSTS-IN-+))
 (15 15 (:TYPE-PRESCRIPTION BOOLEANP))
 (15 9 (:REWRITE DEFAULT-CAR))
 (14 2 (:REWRITE CAR-OF-TAKE))
 (8 8 (:TYPE-PRESCRIPTION NFIX))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 2 (:REWRITE FM9001::NTH-V-NOT))
 (3 3 (:TYPE-PRESCRIPTION FM9001::NAT-TO-V))
 (1 1 (:REWRITE FM9001::V-ZP-AS-AND-CROCK))
 )
