(PLISTP)
(FORMATP)
(GET-SBITS)
(GET-EBITS)
(SGNF)
(EXPF)
(SIGF)
(NORMAL-ENCODING-P
 (13 13 (:TYPE-PRESCRIPTION A14 . 1))
 )
(BITN-0-1)
(BITS-NAT
 (310 101 (:REWRITE DEFAULT-*-2))
 (200 101 (:REWRITE DEFAULT-*-1))
 (103 95 (:REWRITE DEFAULT-+-2))
 (101 95 (:REWRITE DEFAULT-+-1))
 (80 20 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (63 49 (:REWRITE DEFAULT-<-2))
 (56 20 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (52 49 (:REWRITE DEFAULT-<-1))
 (49 7 (:REWRITE DEFAULT-UNARY-/))
 (31 4 (:REWRITE FL-INT))
 (31 4 (:REWRITE A10))
 (25 25 (:REWRITE ZIP-OPEN))
 (20 20 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (20 20 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (20 20 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (18 18 (:LINEAR *-WEAKLY-MONOTONIC . 2))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE A5))
 )
(BITS<
 (477 143 (:REWRITE DEFAULT-*-2))
 (240 15 (:REWRITE FL-INT))
 (240 15 (:REWRITE A10))
 (231 143 (:REWRITE DEFAULT-*-1))
 (212 190 (:REWRITE DEFAULT-+-2))
 (193 190 (:REWRITE DEFAULT-+-1))
 (160 36 (:REWRITE ZIP-OPEN))
 (124 10 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
 (97 69 (:REWRITE DEFAULT-<-2))
 (87 69 (:REWRITE DEFAULT-<-1))
 (60 4 (:REWRITE REARRANGE-NEGATIVE-COEFS-<))
 (55 14 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (43 14 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (42 6 (:REWRITE DEFAULT-UNARY-/))
 (14 14 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (14 14 (:LINEAR *-WEAKLY-MONOTONIC . 2))
 (14 14 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (14 14 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE A5))
 )
(NORMAL-ENCODING-LEMMA
 (654 48 (:DEFINITION EXPT))
 (374 102 (:REWRITE DEFAULT-*-2))
 (296 14 (:REWRITE A10))
 (271 258 (:REWRITE DEFAULT-+-2))
 (258 258 (:REWRITE DEFAULT-+-1))
 (228 102 (:REWRITE DEFAULT-*-1))
 (122 92 (:REWRITE DEFAULT-<-2))
 (116 92 (:REWRITE DEFAULT-<-1))
 (114 114 (:REWRITE DEFAULT-CAR))
 (84 12 (:REWRITE DEFAULT-UNARY-/))
 (46 46 (:REWRITE FOLD-CONSTS-IN-+))
 (45 45 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1))
 )
(DECODE
 (20 20 (:TYPE-PRESCRIPTION A14 . 1))
 )
(REPP
 (40 40 (:TYPE-PRESCRIPTION A14 . 1))
 )
(ENCODE
 (9 9 (:TYPE-PRESCRIPTION A14 . 1))
 )
(CODE-1
 (971 171 (:REWRITE DEFAULT-*-2))
 (789 329 (:REWRITE DEFAULT-+-2))
 (423 329 (:REWRITE DEFAULT-+-1))
 (225 171 (:REWRITE DEFAULT-*-1))
 (177 37 (:REWRITE ZIP-OPEN))
 (171 9 (:REWRITE A10))
 (132 81 (:REWRITE DEFAULT-<-1))
 (120 120 (:REWRITE FOLD-CONSTS-IN-+))
 (90 81 (:REWRITE DEFAULT-<-2))
 (78 78 (:REWRITE DEFAULT-CAR))
 (49 7 (:REWRITE DEFAULT-UNARY-/))
 (38 38 (:REWRITE DEFAULT-CDR))
 (26 26 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (26 26 (:LINEAR *-WEAKLY-MONOTONIC . 1))
 (26 26 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (26 26 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (26 26 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (26 26 (:LINEAR *-STRONGLY-MONOTONIC . 1))
 (13 13 (:REWRITE A5))
 (12 1 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 )
(CODE-2
 (2670 528 (:REWRITE DEFAULT-*-2))
 (1697 944 (:REWRITE DEFAULT-+-2))
 (1060 944 (:REWRITE DEFAULT-+-1))
 (1044 42 (:REWRITE A10))
 (832 528 (:REWRITE DEFAULT-*-1))
 (638 356 (:REWRITE DEFAULT-<-1))
 (476 356 (:REWRITE DEFAULT-<-2))
 (372 72 (:REWRITE DEFAULT-UNARY-/))
 (358 106 (:REWRITE ZIP-OPEN))
 (296 296 (:REWRITE DEFAULT-CAR))
 (251 251 (:REWRITE FOLD-CONSTS-IN-+))
 (186 186 (:REWRITE DEFAULT-CDR))
 (34 34 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (34 34 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (34 34 (:LINEAR *-STRONGLY-MONOTONIC . 1))
 (30 30 (:LINEAR *-WEAKLY-MONOTONIC . 1))
 (25 25 (:REWRITE A5))
 (14 14 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (14 14 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 (8 2 (:REWRITE ABS-POS))
 )
(CODE-3
 (83 8 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (83 8 (:LINEAR *-STRONGLY-MONOTONIC . 1))
 (82 4 (:DEFINITION EXPT))
 (75 8 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (64 2 (:REWRITE A10))
 (49 14 (:REWRITE DEFAULT-<-1))
 (47 17 (:REWRITE DEFAULT-*-2))
 (46 8 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (44 26 (:REWRITE DEFAULT-+-2))
 (41 17 (:REWRITE DEFAULT-*-1))
 (29 26 (:REWRITE DEFAULT-+-1))
 (29 14 (:REWRITE DEFAULT-<-2))
 (14 2 (:REWRITE ZIP-OPEN))
 (14 1 (:REWRITE REARRANGE-NEGATIVE-COEFS-<))
 (12 1 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (8 8 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 )
(CODE-4
 (371 23 (:DEFINITION EXPT))
 (196 62 (:REWRITE DEFAULT-*-2))
 (150 10 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (141 116 (:REWRITE DEFAULT-+-2))
 (133 62 (:REWRITE DEFAULT-*-1))
 (119 116 (:REWRITE DEFAULT-+-1))
 (119 5 (:REWRITE A10))
 (111 53 (:REWRITE DEFAULT-<-1))
 (71 53 (:REWRITE DEFAULT-<-2))
 (69 15 (:REWRITE DEFAULT-UNARY-/))
 (68 10 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (48 10 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (46 46 (:REWRITE DEFAULT-CAR))
 (45 45 (:REWRITE DEFAULT-CDR))
 (30 6 (:REWRITE ZIP-OPEN))
 (28 2 (:REWRITE REARRANGE-NEGATIVE-COEFS-<))
 (24 2 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
 (10 10 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (10 10 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 )
(NORMAL-NON-ZERO
 (491 29 (:DEFINITION EXPT))
 (276 67 (:REWRITE DEFAULT-*-2))
 (213 149 (:REWRITE DEFAULT-+-2))
 (169 7 (:REWRITE A10))
 (161 149 (:REWRITE DEFAULT-+-1))
 (127 67 (:REWRITE DEFAULT-*-1))
 (67 49 (:REWRITE DEFAULT-<-2))
 (65 49 (:REWRITE DEFAULT-<-1))
 (58 58 (:REWRITE DEFAULT-CAR))
 (51 51 (:REWRITE DEFAULT-CDR))
 (35 5 (:REWRITE DEFAULT-UNARY-/))
 (25 25 (:REWRITE FOLD-CONSTS-IN-+))
 (20 8 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE A5))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
 (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
 (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1))
 )
(CODE-5
 (7530 296 (:DEFINITION EXPT))
 (3655 1084 (:REWRITE DEFAULT-*-2))
 (3111 1988 (:REWRITE DEFAULT-+-2))
 (2360 110 (:REWRITE FL-INT))
 (2360 110 (:REWRITE A10))
 (2142 1988 (:REWRITE DEFAULT-+-1))
 (2089 1084 (:REWRITE DEFAULT-*-1))
 (1508 160 (:REWRITE ZIP-OPEN))
 (964 964 (:TYPE-PRESCRIPTION INTEGERP-REM))
 (866 866 (:REWRITE DEFAULT-CDR))
 (681 579 (:REWRITE DEFAULT-<-1))
 (581 579 (:REWRITE DEFAULT-<-2))
 (556 556 (:REWRITE DEFAULT-CAR))
 (230 230 (:REWRITE FOLD-CONSTS-IN-+))
 (222 10 (:DEFINITION EXPO1))
 (210 30 (:REWRITE DEFAULT-UNARY-/))
 (194 10 (:DEFINITION EXPO2))
 (94 30 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (88 4 (:REWRITE RATIONALP-*))
 (45 21 (:REWRITE A5))
 (44 30 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (30 30 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (30 30 (:LINEAR *-WEAKLY-MONOTONIC . 1))
 (30 30 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (30 30 (:LINEAR *-STRONGLY-MONOTONIC . 1))
 (8 2 (:REWRITE RATIONALP-+))
 (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 2))
 (4 4 (:LINEAR FL-WEAKLY-MONOTONIC . 1))
 (2 2 (:REWRITE A3))
 )
(CODE-6
 (2557 2557 (:TYPE-PRESCRIPTION A14 . 1))
 (2258 68 (:DEFINITION EXPT))
 (1069 227 (:REWRITE DEFAULT-*-2))
 (655 372 (:REWRITE DEFAULT-+-2))
 (511 372 (:REWRITE DEFAULT-+-1))
 (447 227 (:REWRITE DEFAULT-*-1))
 (416 116 (:REWRITE A4))
 (252 60 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (240 68 (:REWRITE ZIP-OPEN))
 (202 110 (:REWRITE DEFAULT-<-1))
 (200 52 (:REWRITE DEFAULT-UNARY-MINUS))
 (188 60 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (188 60 (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (160 110 (:REWRITE DEFAULT-<-2))
 (124 60 (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (96 38 (:REWRITE UNICITY-OF-0))
 (36 36 (:REWRITE FOLD-CONSTS-IN-+))
 (19 19 (:REWRITE A5))
 )
(CODE-A
 (511 15 (:DEFINITION EXPT))
 (418 179 (:REWRITE DEFAULT-*-2))
 (239 179 (:REWRITE DEFAULT-*-1))
 (229 15 (:REWRITE ZIP-OPEN))
 (195 9 (:DEFINITION EXPO1))
 (169 9 (:DEFINITION EXPO2))
 (148 116 (:REWRITE DEFAULT-+-2))
 (130 116 (:REWRITE DEFAULT-+-1))
 (105 96 (:REWRITE DEFAULT-<-1))
 (98 96 (:REWRITE DEFAULT-<-2))
 (44 24 (:REWRITE A5))
 (26 8 (:REWRITE UNICITY-OF-0))
 )
(CODE-B
 (5 5 (:TYPE-PRESCRIPTION A14 . 1))
 )
(CODE-C
 (5 5 (:TYPE-PRESCRIPTION A14 . 1))
 )
(EXACTP-DECODE
 (1360 19 (:DEFINITION EXPT))
 (507 170 (:REWRITE DEFAULT-*-2))
 (416 19 (:REWRITE ZIP-OPEN))
 (374 223 (:REWRITE DEFAULT-+-2))
 (339 15 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
 (305 223 (:REWRITE DEFAULT-+-1))
 (212 58 (:REWRITE A4))
 (176 170 (:REWRITE DEFAULT-*-1))
 (160 8 (:DEFINITION EXPO1))
 (144 8 (:DEFINITION EXPO2))
 (120 37 (:REWRITE UNICITY-OF-0))
 (87 77 (:REWRITE DEFAULT-<-1))
 (85 77 (:REWRITE DEFAULT-<-2))
 (27 11 (:REWRITE A5))
 (24 24 (:REWRITE FOLD-CONSTS-IN-+))
 )
(EXPT+EXPT
 (110 23 (:REWRITE DEFAULT-*-2))
 (44 44 (:REWRITE DEFAULT-+-2))
 (44 44 (:REWRITE DEFAULT-+-1))
 (23 23 (:REWRITE DEFAULT-*-1))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 )
(BAD-HACK)
(CODE-D
 (803 464 (:REWRITE DEFAULT-+-2))
 (614 144 (:REWRITE DEFAULT-*-2))
 (554 464 (:REWRITE DEFAULT-+-1))
 (368 368 (:REWRITE DEFAULT-CDR))
 (257 104 (:REWRITE A4))
 (238 165 (:REWRITE DEFAULT-<-1))
 (213 52 (:REWRITE ZIP-OPEN))
 (201 165 (:REWRITE DEFAULT-<-2))
 (188 188 (:REWRITE DEFAULT-CAR))
 (151 144 (:REWRITE DEFAULT-*-1))
 (147 7 (:REWRITE REARRANGE-NEGATIVE-COEFS-EQUAL))
 (56 21 (:REWRITE UNICITY-OF-0))
 (33 33 (:REWRITE FOLD-CONSTS-IN-+))
 )
