(Y86-OF)
(INTEGERP-Y86-OF)
(Y86-OF-LESS-THAN-2)
(!Y86-OF)
(INTEGERP-!Y86-OF)
(!Y86-OF-LESS-THAN-EXPT-2-32)
(Y86-SF)
(INTEGERP-Y86-SF)
(Y86-SF-LESS-THAN-2)
(!Y86-SF)
(!Y86-SF-LESS-THAN-EXPT-2-32)
(INTEGERP-!Y86-SF)
(Y86-ZF)
(INTEGERP-Y86-ZF)
(Y86-ZF-LESS-THAN-2)
(!Y86-ZF)
(INTEGERP-!Y86-ZF)
(!Y86-ZF-LESS-THAN-EXPT-2-32)
(Y86-CONDITION
 (120 60 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (19 19 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (16 9 (:REWRITE DEFAULT-<-1))
 (15 6 (:REWRITE DEFAULT-+-2))
 (15 6 (:REWRITE DEFAULT-+-1))
 (12 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:REWRITE DEFAULT-<-2))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(INTEGERP-Y86-CONDITION)
(Y86-CONDITION-LESS
 (22 1 (:REWRITE DEFAULT-<-1))
 (21 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (15 6 (:REWRITE DEFAULT-+-2))
 (15 6 (:REWRITE DEFAULT-+-1))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(Y86-HALT
 (12 6 (:TYPE-PRESCRIPTION NATP-EIP))
 )
(Y86-HALT-PRESERVES-X86-32P
 (68 34 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-NOP
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (10 6 (:REWRITE DEFAULT-<-2))
 (8 6 (:REWRITE DEFAULT-<-1))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-NOP-PRESERVES-X86-32P
 (104 52 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (5 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (4 3 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(Y86-CMOVE
 (112 56 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (48 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (43 23 (:REWRITE DEFAULT-<-1))
 (31 23 (:REWRITE DEFAULT-<-2))
 (18 12 (:REWRITE DEFAULT-+-2))
 (18 12 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-CMOVE-PRESERVES-X86-32P
 (332 166 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (34 18 (:REWRITE DEFAULT-+-2))
 (30 6 (:LINEAR LOGIOR-<=-EXPT-2-TO-N))
 (24 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (20 18 (:REWRITE DEFAULT-+-1))
 (20 4 (:LINEAR LOGIOR-LESS-THAN-OR-EQUAL))
 (16 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (10 10 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-MOVE-IMM
 (783 27 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (320 160 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (297 3 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (294 3 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (216 27 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (186 96 (:REWRITE DEFAULT-<-2))
 (153 96 (:REWRITE DEFAULT-<-1))
 (56 34 (:REWRITE DEFAULT-+-2))
 (46 34 (:REWRITE DEFAULT-+-1))
 (42 18 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (10 10 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-MOVE-IMM-PRESERVES-X86-32P
 (783 27 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (312 156 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (297 3 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (294 3 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (216 27 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (160 76 (:REWRITE DEFAULT-<-2))
 (112 76 (:REWRITE DEFAULT-<-1))
 (33 18 (:REWRITE DEFAULT-+-2))
 (21 18 (:REWRITE DEFAULT-+-1))
 (15 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 8 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RA-TO-MEM-AT-RB+D
 (256 128 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (232 8 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (85 42 (:REWRITE DEFAULT-<-1))
 (75 42 (:REWRITE DEFAULT-<-2))
 (65 34 (:REWRITE DEFAULT-+-2))
 (64 8 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (60 20 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (57 34 (:REWRITE DEFAULT-+-1))
 (10 10 (:LINEAR INDEX-OF-<-LEN))
 (10 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(Y86-RA-TO-MEM-AT-RB+D-PRESERVES-X86-32P
 (212 106 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (116 4 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (61 27 (:REWRITE DEFAULT-+-2))
 (41 27 (:REWRITE DEFAULT-+-1))
 (36 16 (:REWRITE DEFAULT-<-1))
 (32 4 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (30 16 (:REWRITE DEFAULT-<-2))
 (12 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-MEM-AT-RA+D-TO-RB
 (256 128 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (232 8 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (75 42 (:REWRITE DEFAULT-<-2))
 (75 42 (:REWRITE DEFAULT-<-1))
 (64 8 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (60 20 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (59 34 (:REWRITE DEFAULT-+-2))
 (51 34 (:REWRITE DEFAULT-+-1))
 (10 10 (:LINEAR INDEX-OF-<-LEN))
 (10 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(Y86-MEM-AT-RA+D-TO-RB-PRESERVES-X86-32P
 (236 118 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (116 4 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (81 36 (:REWRITE DEFAULT-+-2))
 (57 36 (:REWRITE DEFAULT-+-1))
 (32 4 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (30 16 (:REWRITE DEFAULT-<-2))
 (30 16 (:REWRITE DEFAULT-<-1))
 (12 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-ALU-RESULTS-STORE-FLGS
 (180 90 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (28 20 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-<-2))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-ALU-RESULTS-STORE-FLGS-PRESERVES-X86-32P
 (140 70 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(HACK-1
 (798 2 (:REWRITE X86-32P-!EIP))
 (792 2 (:REWRITE Y86-ALU-RESULTS-STORE-FLGS-PRESERVES-X86-32P))
 (786 2 (:REWRITE X86-32P-!RGFI-N03P))
 (270 2 (:LINEAR N30P-LOGXOR-N30P-LESS-THAN-1073741824))
 (270 2 (:LINEAR N24P-LOGXOR-N24P-LESS-THAN-16777216))
 (270 2 (:LINEAR N20P-LOGXOR-N20P-LESS-THAN-1048576))
 (270 2 (:LINEAR N16P-LOGXOR-N16P-LESS-THAN-65536))
 (270 2 (:LINEAR N12P-LOGXOR-N12P-LESS-THAN-4096))
 (270 2 (:LINEAR N08P-LOGXOR-N08P-LESS-THAN-256))
 (270 2 (:LINEAR N05P-LOGXOR-N05P-LESS-THAN-32))
 (270 2 (:LINEAR N04P-LOGXOR-N04P-LESS-THAN-16))
 (270 2 (:LINEAR N03P-LOGXOR-N03P-LESS-THAN-8))
 (270 2 (:LINEAR N02P-LOGXOR-N02P-LESS-THAN-4))
 (270 2 (:LINEAR N01P-LOGXOR-N01P-LESS-THAN-2))
 (264 132 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (139 139 (:TYPE-PRESCRIPTION NATP))
 (96 30 (:REWRITE DEFAULT-<-1))
 (38 19 (:REWRITE DEFAULT-+-2))
 (32 30 (:REWRITE DEFAULT-<-2))
 (20 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (19 19 (:REWRITE DEFAULT-+-1))
 (18 2 (:LINEAR LOGXOR-<=-EXPT-2-TO-N))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RA-XOR-RB-TO-RB
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (77 28 (:REWRITE DEFAULT-<-1))
 (46 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (36 28 (:REWRITE DEFAULT-<-2))
 (18 12 (:REWRITE DEFAULT-+-2))
 (18 12 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RA-XOR-RB-TO-RB-PRESERVES-X86-32P
 (945 7 (:LINEAR N30P-LOGXOR-N30P-LESS-THAN-1073741824))
 (945 7 (:LINEAR N24P-LOGXOR-N24P-LESS-THAN-16777216))
 (945 7 (:LINEAR N20P-LOGXOR-N20P-LESS-THAN-1048576))
 (945 7 (:LINEAR N16P-LOGXOR-N16P-LESS-THAN-65536))
 (945 7 (:LINEAR N12P-LOGXOR-N12P-LESS-THAN-4096))
 (945 7 (:LINEAR N08P-LOGXOR-N08P-LESS-THAN-256))
 (945 7 (:LINEAR N05P-LOGXOR-N05P-LESS-THAN-32))
 (945 7 (:LINEAR N04P-LOGXOR-N04P-LESS-THAN-16))
 (945 7 (:LINEAR N03P-LOGXOR-N03P-LESS-THAN-8))
 (945 7 (:LINEAR N02P-LOGXOR-N02P-LESS-THAN-4))
 (945 7 (:LINEAR N01P-LOGXOR-N01P-LESS-THAN-2))
 (456 228 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (363 97 (:REWRITE DEFAULT-<-1))
 (181 181 (:TYPE-PRESCRIPTION NATP))
 (104 53 (:REWRITE DEFAULT-+-2))
 (102 97 (:REWRITE DEFAULT-<-2))
 (63 7 (:LINEAR LOGXOR-<=-EXPT-2-TO-N))
 (60 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (55 53 (:REWRITE DEFAULT-+-1))
 (50 10 (:LINEAR LOGIOR-<=-EXPT-2-TO-N))
 (35 7 (:LINEAR LOGIOR-LESS-THAN-OR-EQUAL))
 (16 16 (:LINEAR INDEX-OF-<-LEN))
 )
(HACK-2
 (1232 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (1220 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (808 2 (:REWRITE X86-32P-!EIP))
 (802 2 (:REWRITE Y86-ALU-RESULTS-STORE-FLGS-PRESERVES-X86-32P))
 (796 2 (:REWRITE X86-32P-!RGFI-N03P))
 (472 102 (:REWRITE DEFAULT-<-1))
 (264 132 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (139 139 (:TYPE-PRESCRIPTION NATP))
 (104 102 (:REWRITE DEFAULT-<-2))
 (38 19 (:REWRITE DEFAULT-+-2))
 (20 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (19 19 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RA-AND-RB-TO-RB
 (136 28 (:REWRITE DEFAULT-<-1))
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (44 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (36 28 (:REWRITE DEFAULT-<-2))
 (18 12 (:REWRITE DEFAULT-+-2))
 (18 12 (:REWRITE DEFAULT-+-1))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RA-AND-RB-TO-RB-PRESERVES-X86-32P
 (1433 297 (:REWRITE DEFAULT-<-1))
 (380 190 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (301 297 (:REWRITE DEFAULT-<-2))
 (143 143 (:TYPE-PRESCRIPTION NATP))
 (82 42 (:REWRITE DEFAULT-+-2))
 (54 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (45 9 (:LINEAR LOGIOR-<=-EXPT-2-TO-N))
 (44 42 (:REWRITE DEFAULT-+-1))
 (30 6 (:LINEAR LOGIOR-LESS-THAN-OR-EQUAL))
 (14 14 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RA-+-RB-TO-RB
 (200 100 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (186 40 (:REWRITE DEFAULT-<-1))
 (50 24 (:REWRITE DEFAULT-+-2))
 (49 40 (:REWRITE DEFAULT-<-2))
 (42 24 (:REWRITE DEFAULT-+-1))
 (15 3 (:LINEAR LOGIOR-<=-EXPT-2-TO-N))
 (10 2 (:LINEAR LOGIOR-LESS-THAN-OR-EQUAL))
 (10 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:LINEAR INDEX-OF-<-LEN))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(Y86-RA-+-RB-TO-RB-PRESERVES-X86-32P
 (3289 557 (:REWRITE DEFAULT-<-1))
 (1100 550 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (567 557 (:REWRITE DEFAULT-<-2))
 (313 144 (:REWRITE DEFAULT-+-2))
 (224 144 (:REWRITE DEFAULT-+-1))
 (135 27 (:LINEAR LOGIOR-<=-EXPT-2-TO-N))
 (90 18 (:LINEAR LOGIOR-LESS-THAN-OR-EQUAL))
 (88 88 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (38 38 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RB---RA-TO-RB
 (312 35 (:REWRITE DEFAULT-<-1))
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (43 35 (:REWRITE DEFAULT-<-2))
 (40 22 (:REWRITE DEFAULT-+-1))
 (30 22 (:REWRITE DEFAULT-+-2))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(Y86-RB---RA-TO-RB-PRESERVES-X86-32P
 (17280 128 (:DEFINITION NATP))
 (15752 3517 (:REWRITE DEFAULT-<-1))
 (3527 3517 (:REWRITE DEFAULT-<-2))
 (1124 562 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (342 151 (:REWRITE DEFAULT-+-2))
 (234 151 (:REWRITE DEFAULT-+-1))
 (135 27 (:LINEAR LOGIOR-<=-EXPT-2-TO-N))
 (128 128 (:TYPE-PRESCRIPTION NATP))
 (112 28 (:REWRITE DEFAULT-UNARY-MINUS))
 (90 18 (:LINEAR LOGIOR-LESS-THAN-OR-EQUAL))
 (62 62 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (38 38 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-CJUMP
 (188 94 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (22 16 (:REWRITE DEFAULT-<-1))
 (21 16 (:REWRITE DEFAULT-<-2))
 (20 10 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (18 12 (:REWRITE DEFAULT-+-2))
 (18 12 (:REWRITE DEFAULT-+-1))
 (8 8 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-CJUMP-PRESERVES-X86-32P
 (272 136 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (16 9 (:REWRITE DEFAULT-+-2))
 (14 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 9 (:REWRITE DEFAULT-+-1))
 (8 8 (:LINEAR INDEX-OF-<-LEN))
 (6 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(Y86-CALL
 (108 54 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (45 18 (:REWRITE DEFAULT-<-1))
 (22 14 (:REWRITE DEFAULT-+-2))
 (21 18 (:REWRITE DEFAULT-<-2))
 (20 14 (:REWRITE DEFAULT-+-1))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-CALL-PRESERVES-X86-32P
 (128 64 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (22 12 (:REWRITE DEFAULT-+-2))
 (14 12 (:REWRITE DEFAULT-+-1))
 (9 6 (:REWRITE DEFAULT-<-1))
 (8 6 (:REWRITE DEFAULT-<-2))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RET
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (23 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 6 (:REWRITE DEFAULT-+-2))
 (9 6 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-RET-PRESERVES-X86-32P
 (92 46 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-PUSHL
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (54 25 (:REWRITE DEFAULT-<-1))
 (33 25 (:REWRITE DEFAULT-<-2))
 (33 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (22 14 (:REWRITE DEFAULT-+-2))
 (20 14 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-PUSHL-PRESERVES-X86-32P
 (164 82 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (83 24 (:REWRITE DEFAULT-<-1))
 (26 24 (:REWRITE DEFAULT-<-2))
 (26 14 (:REWRITE DEFAULT-+-2))
 (16 14 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-POPL
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (48 25 (:REWRITE DEFAULT-<-1))
 (33 25 (:REWRITE DEFAULT-<-2))
 (33 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 16 (:REWRITE DEFAULT-+-2))
 (24 16 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-POPL-PRESERVES-X86-32P
 (164 82 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (76 22 (:REWRITE DEFAULT-<-1))
 (24 22 (:REWRITE DEFAULT-<-2))
 (19 11 (:REWRITE DEFAULT-+-2))
 (16 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (14 11 (:REWRITE DEFAULT-+-1))
 (6 6 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-IMM-ADD
 (522 18 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (264 132 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (198 2 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (198 2 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (198 2 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (196 2 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (170 38 (:REWRITE DEFAULT-+-2))
 (146 74 (:REWRITE DEFAULT-<-1))
 (144 18 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (137 74 (:REWRITE DEFAULT-<-2))
 (116 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (109 38 (:REWRITE DEFAULT-+-1))
 (48 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:LINEAR INDEX-OF-<-LEN))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 )
(Y86-IMM-ADD-PRESERVES-X86-32P
 (783 27 (:LINEAR ASH-NEGATIVE-SHIFT-MAKES-INPUT-SMALLER))
 (336 168 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (297 3 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (294 3 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (216 27 (:LINEAR RM08-LESS-THAN-EXPT-2-32))
 (162 78 (:REWRITE DEFAULT-<-2))
 (122 78 (:REWRITE DEFAULT-<-1))
 (53 24 (:REWRITE DEFAULT-+-2))
 (33 24 (:REWRITE DEFAULT-+-1))
 (15 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 8 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-LEAVE
 (88 44 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (20 15 (:REWRITE DEFAULT-<-1))
 (19 15 (:REWRITE DEFAULT-<-2))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-LEAVE-PRESERVES-X86-32P
 (128 64 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 4 (:REWRITE DEFAULT-<-2))
 (5 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (4 3 (:REWRITE DEFAULT-+-1))
 )
(Y86-ILLEGAL-OPCODE
 (40 20 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (12 6 (:TYPE-PRESCRIPTION NATP-RM08))
 )
(Y86-ILLEGAL-OPCODE-PRESERVES-X86-32P
 (68 34 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86-STEP
 (40 20 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (32 26 (:TYPE-PRESCRIPTION NATP-RM08))
 )
(Y86-STEP-PRESERVES-X86-32P
 (142 57 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (68 34 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 )
(Y86
 (192 96 (:TYPE-PRESCRIPTION NATP-NTH-OF-RGF))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(Y86-PRESERVES-X86-32P
 (14 14 (:LINEAR INDEX-OF-<-LEN))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
